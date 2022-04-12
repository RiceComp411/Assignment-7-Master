import java.io.*;
import java.util.*;
import java.text.*;
import java.util.ArrayList;
import java.util.Arrays;

/* An implementation of the Jam language consisting of a parser, a static distance coordinate converter,
 * and three interpreters:
 * - a conventional symbolic AST interper;
 * - a high-level static distance coordinate (SD) AST interpreter
 * - a low-level SD AST interpreter with an explicit heap, environment stack [to hold the static chain the absence of
 *   CpS conversion] and a temps stack.
 * The explicit heap is managed using a Cheney copying collector that allocates a new heap and copies the live data 
 * from the old heap to the new heap.  The environment stack and temps stack hold all of the heap roots.  If the code
 * is CPSed the environment static consists of a single int cell pointing to the environment (a linked list of activation 
 * records) in the heap.
 */

/** Interpreter Classes */

/** The exception class for Jam run-time errors */
class EvalException extends RuntimeException {
  EvalException(String msg) { super(msg); }
}

/** The visitor interface for interpreting both SymASTs and SDASTs which share many AST classes.  These shared classes
  * are identified in the ComASTVisitor interface.
  * There are three inmmediate extensions of ComASTVisitor: SymASTVisitor identifying the SymAST classes, SDASTVisitor
  * identifying the SDAST classes, and ASTVisitor which is effectively the union of SymASTVisitor and
  * SDASTVisitor.  In this code, every ASTVisitor is either a SymASTVisior or a SDASTVisitor (where the unused visitor
  * methods have a default meaning that immeidately aborts execution. 
  * The EvalVisitor interface adds methods to ASTVisitor that create subordinate visitors (of the appropriate form) to 
  * handle the particular ASTs that require further polymorphic adaptation (UnOpApps, BinOpApps, and [Function] Apps).
  */
interface EvalVisitor extends ASTVisitor<JamVal> {
  
  /** Returns the environment embedded in this EvalVisitor */
  Environment env();
  
  /** Constructs a UnOpVisitor with the specified evaluated arg. */
  UnOpVisitor<JamVal> newUnOpVisitor(JamVal arg);
  
  /** Constructs a BinOpVisitor with the specified unevaluated arguments. */
  BinOpVisitor<JamVal> newBinOpVisitor(AST arg1, AST arg2);
  
  /** Constructs a FunVisitor (to process a Function App) with the specified array of unevaluated arguments. */
  FunVisitor<JamVal> newFunVisitor(AST args[]);
}

/** The visitor interface for interpreting SDAST's */
interface SDEvalVisitor extends SDASTVisitor<Interpreter.Heap.HeapPtr> {
  int env();
}
  
/** Interpreter class that supports both conventional eager evaluation and RAM-based eager evaluation of SymAST and 
  * SDAST programs. */
class Interpreter {
  
  /* Constants for the low-level interpreter */
  public static final int DEPTH_BOUND      = 32;
  public static final int STACKSIZE        = 1<<14;
  public static final int TEMPSSIZE        = 1<<8;
  public static final int DEFAULT_HEAPSIZE = 1<<20;
  
  /** Primary fields */
  private Parser parser;
  private SConverter sConverter;
  
  /** The SymAST evlauator*/
  private SymEvaluator symEvaluator;    
  
  /** The SDAST evaluators */
  private SDEvaluator sdEvaluator;         /* high-level SDAST Evaluator */
  private Heap.RamSDEvaluator ramSdEvaluator;  /* low-level SDAST Evaluator */ 

  public static int HEAPSIZE;
  
  /** The stack and heap for the simulated RAM machine */
  private Heap heap;   // not final because GC allocates new hea
  
  /* Constructors */
  Interpreter(Parser p, int heapSize) {  
    parser = p;
    sConverter = p.sConverter();
    symEvaluator = new SymEvaluator(EmptyVarEnv.ONLY); 
    sdEvaluator = new SDEvaluator(EmptySDEnv.ONLY);
    
    /* Before defininig ramSDEvaluator [the low-level SDAST evalutor}, the variables heap, stack [of environments], and
     * temps [stack of temporaries] must be set up.
    
    /* create a new RamSDEvaluator with an empty temps stack and env stack with empty environment as only entry */
    heap = new Heap(heapSize);
    ramSdEvaluator = heap.newRamSDEvaluator();
//    System.err.println("stack = " + stack);
//    System.err.println("temps = " + temps);
  }  
  
  Interpreter(Parser p) { this(p, DEFAULT_HEAPSIZE); }
  Interpreter(String fileName) throws IOException { this(new Parser(fileName), DEFAULT_HEAPSIZE); }
  Interpreter(String fileName, int heapSize) throws IOException {this(new Parser(fileName), heapSize); }
  Interpreter(Reader reader, int heapsize) { this(new Parser(reader), heapsize); }
  Interpreter(Reader reader) { this(new Parser(reader), DEFAULT_HEAPSIZE); }
  
  public static void Assert(boolean b) {
    if (! b) throw new EvalException("Assertion failure!");
  }
  
  /* Anonymous inner class that implements the arity operation on each of the primitive Jam functions.
   * It is applicable to the interpretation of both SDASTs and SymASTs.   No GC can happen during its execution. */
  PrimFunVisitor<IntConstant> primArityEvaluator = new
    PrimFunVisitor<IntConstant>() { /* ANONYMOUS CLASS */
    
    public IntConstant forFunctionPPrim() { return new IntConstant(1); }
    public IntConstant forNumberPPrim()   { return new IntConstant(1); }
    public IntConstant forListPPrim()     { return new IntConstant(1); }
    public IntConstant forConsPPrim()     { return new IntConstant(1); }
    public IntConstant forEmptyPPrim()     { return new IntConstant(1); }
    public IntConstant forRefPPrim()      { return new IntConstant(1); }
    
    public IntConstant forArityPrim() { return new IntConstant(1); }
    
    public IntConstant forConsPrim() { return new IntConstant(2); }
    public IntConstant forFirstPrim() { return new IntConstant(1); }
    public IntConstant forRestPrim() { return new IntConstant(1); }
    
    public IntConstant forAsBoolPrim() { return new IntConstant(1); }
  };   
  
  /* Returns parsed program in unshadowed SymAST form, parsing the program from file and checking it if necessary. */
  public SymAST getUSAST() { return parser.checkAndUnshadowProg(); }
  
  /* Returns parsed program in SDAST form, parsing the program from text, checking it, and converting it, if necessary. */ 
  public SDAST getSDAST() { return parser.sdConvertProg(); }
  
  /* Returns String representation of parsed program in SymAST form. */
  public String getRawProg() { return parser.parseProg().toString(); }
  
  /* Returns String representation of the parsed program in unshadowed SymAST form. */ 
  public String getUSProg() { return getUSAST().toString(); }
  
  /* Returns String representation of the parsed program in SDAST form. */ 
  public String getSDProg() { return getSDAST().toString(); }
  
  /** Parses, checks, unshadows, and interprets the input embeded in parser */
  public JamVal eval() {
    SymAST unshadowedProg = getUSAST();
    return unshadowedProg.accept(symEvaluator); 
  }
  
  /** Parses, checks, unshadowws, CPS converts, and interprets the input embedded in the parser */
  public JamVal cpsEval() {
    SymAST prog = parser.cpsProg();
    return prog.accept(symEvaluator);
  }
  
  /** Parses, checks, and interprets the input embeded in parser using static distance interpreter */
  public JamVal SDEval() {  // Note: should be named sdEval
    SDAST prog = getSDAST();
    return prog.accept(sdEvaluator); 
  }
  
  /** Parses, checks, CPS converts, and interprets the input embedded in the parser using explicit heap */
  public JamVal sdCpsEval() {
    SDAST prog = parser.sdCpsConvertProg();
    return prog.accept(sdEvaluator);
  }
  
  /** Parses, checks, and interprets the input embeded in parser using explicit heap */
  public JamVal ramSDEval() {
    SDAST prog = getSDAST();
    return prog.accept(ramSdEvaluator).decode(); 
  }
  
  /** Parses, checks, CPS converts, and interprets the input embedded in the parser using explicit heap */
  public JamVal ramSDCpsEval() {
    SDAST prog = parser.sdCpsConvertProg();
    return prog.accept(ramSdEvaluator).decode();
  }
  
  public AST unshadow() {
    SymAST prog = parser.checkAndUnshadowProg();
    return prog;
  }
  
  public SDAST convertToSD() {
    SDAST prog = parser.sdConvertProg();
    return prog;
  }
  
  public AST convertToCPS() { return parser.cpsProg(); }
  
  public int[] getMemory() { return heap.getCells(); }
  
  public int getTempsSize() { return heap.getTempsSize(); }
  
  
  /*  Inner classes: SymClosure, SDClosure, Evaluator, SymEvaluator, SDEvaluator.  The Sym/SD versions are very
   *  similar but I do not see how to share code effectively, other than the part factored out in Evaluator.  */
  
  /** SymClosure: a Jam closure for programs with symbolic variables.  */
  static class SymClosure extends JamFun implements Closure {
    private Map map;
    private SymEvaluator eval;
    SymClosure(Map m, SymEvaluator e) { map = m; eval = e; }
    //  VarEnv env() { return env; }
    public int arity() { return map.vars().length; }
    public JamVal apply(JamVal[] args) {
      Variable[] vars = map.vars();
      VarEnv newEnv = eval.env();
      int n = vars.length;
      if (n != args.length) throw new EvalException("closure " + this + " applied to " + 
                                                    args.length + " arguments instead of " + n + " arguments");
      for (int i = n-1 ; i >= 0; i--) 
        newEnv = newEnv.cons(new Binding(vars[i],args[i]));
      return map.body().accept((SymASTVisitor<JamVal>) eval.newEvalVisitor(newEnv));
    }                                                 
    public <RtnType> RtnType accept(FunVisitor<RtnType> jfv) { return jfv.forClosure(this); }
    public String toString() { return "SymClosure<" + map + ">"; }
  }
  
  /** SDClosure: a Jam closure for programs with static distance coordinates. */
  class SDClosure extends JamFun implements Closure {
    private SMap smap;
    private SDEvaluator eval;
    SDClosure(SMap sm, SDEvaluator e) { smap = sm; eval = e; }
    public int arity() { return smap.arity(); }
    public JamVal apply(JamVal[] args) {
      SDEnv newEnv = eval.env().cons(args);
      int n = arity();
      if (n != args.length) throw new 
        EvalException("closure " + this + " applied to " + args.length + " arguments instead of " + n + " arguments");
      return smap.body().accept((SDASTVisitor<JamVal>) eval.newEvalVisitor(newEnv));
    }                                                    
    public <RtnType> RtnType accept(FunVisitor<RtnType> jfv) { return jfv.forClosure(this); }
    public String toString() { return "SDClosure<" + smap + ">"; }
  }
  
  /** General visitor class for performing HIGH-LEVEL interpretation; provides ComASTVistor methods.  Leaves unique 
    * SymAST and SDAST behavior to more specialized derived classes. 
    * NOTE: I highly recommend following a naming convention for type parameters.  I end all such names with the suffix
    * "Type" and I avoid using the word "Type" as part of any other variable or field names.
    */
  abstract class Evaluator<EnvType extends Environment> implements EvalVisitor {
    
    /* This class which performs high-level interpretation shared between assumes that:
     * - OpTokens are unique.
     * - The only objects used as boolean Jam values (BoolConstants) are BoolConstant.TRUE and BoolConstant.FALSE
     * 
     * Hence,  == can be used to compare OpTokens, and BoolConstants but general equality comparison on JamVals must 
     * still be performed with equals. */
    
    EnvType env;
    
    Evaluator(EnvType e) { env = e; }
    
    /* EvalVisitor methods */
    
    /** getter for env field */
    public EnvType env() { return env; }
    
    public JamVal[] evalArgs(AST[] args) {
      int n = args.length;
      JamVal[] vals = new JamVal[n];
      for (int i = 0; i < n; i++) vals[i] = args[i].accept(this);
      return vals;
    }
    
    public UnOpVisitor<JamVal> newUnOpVisitor(JamVal arg) { return new UnOpEvaluator(arg); }
    public BinOpVisitor<JamVal> newBinOpVisitor(AST arg1, AST arg2) { return new BinOpEvaluator(arg1, arg2); }
    public FunVisitor<JamVal> newFunVisitor(AST args[]) { return new FunEvaluator(evalArgs(args)); }
    public JamVal forDefault(AST a) { throw new EvalException(a + " is not in the domain of the visitor " + getClass()); }
    public JamVal forBoolConstant(BoolConstant b) { return b; }
    public JamVal forIntConstant(IntConstant i) { return i; }
    public JamVal forEmptyConstant(EmptyConstant n) { return JamEmpty.ONLY; }
    public JamVal forPrimFun(PrimFun f) { return f; }  /* all PrimFuns are JamVals */
    public JamVal forUnOpApp(UnOpApp u) { return u.rator().accept(newUnOpVisitor(u.arg().accept(this))); }
    public JamVal forBinOpApp(BinOpApp b) { return b.rator().accept(newBinOpVisitor(b.arg1(), b.arg2())); }
    
    public JamVal forApp(App a) {
      JamVal rator = a.rator().accept(this);
      if (rator instanceof JamFun)  {
        //System.err.println(Evaluator.this);
        //System.err.println(newFunVisitor(a.args()).getClass());
        return ((JamFun) rator).accept(newFunVisitor(a.args()));
      }
      throw new EvalException(rator + " appears at head of application " + a  + " but it is not a valid function");
    }
    
    public JamVal forIf(If i) {
      JamVal test = i.test().accept(this);
      if (! (test instanceof BoolConstant))
        throw new EvalException("non Boolean " + test + " used as test in if");
      if (test == BoolConstant.TRUE) return i.conseq().accept(this);
      return i.alt().accept(this);
    }
    
    /** Visitor for blocks. */
    public JamVal forBlock(Block b) {
      AST[] exps = b.exps();
      int n = exps.length;
      for (int i = 0; i < n-1; i++) exps[i].accept(this);
      return exps[n-1].accept(this);
    }
    
    /** Visitor method for letcc.  In both SymASTs and SDASTs, a Letcc node is illegal in interpreted code; it throws an 
      * exception in this context. In SymASTs, it is legal in programs that are converted to CPS, which eliminates it. */
    public JamVal forLetcc(Letcc host) { return forDefault(host); }
    
    /** Remaining visitor methods are abstract because they are implemented differently in SymASTs and SDASTs */
    public abstract JamVal forVariable(Variable host);
    public abstract JamVal forMap(Map host);
    public abstract JamVal forLet(Let host);
    public abstract JamVal forLetRec(LetRec host);
    
    public abstract JamVal forSDPair(SDPair host);
    public abstract JamVal forSMap(SMap host);
    public abstract JamVal forSLet(SLet host);
    public abstract JamVal forSLetRec(SLetRec host);
    
    /* Inner classes of Evaluator: FunEvaluator, UnOpEvaluator, BinOpEvaluator, primVisitor (anonymous inner class) */
    
    /* Visitor interface for processing the polymrphism in App AST nodes; FunEvaluator may be be the best name choice. */
    
    class FunEvaluator implements FunVisitor<JamVal> {
      
      /** Evaluated arguments */
      JamVal[] vals;
      
      /** Number of arguments */
      int arity;
      
      FunEvaluator(JamVal[] jvs) {
        vals = jvs;
        arity = vals.length;
        // System.err.println("FunEvaluator created with vals = " + ToString.toString(vals, ","));
      }
      
      public JamVal forPrimFun(PrimFun primFun) { return primFun.accept(primEvaluator); }
      public JamVal forClosure(Closure c) { return c.apply(vals);}
      
      /* Fields bound to anonymous inner classes */
      PrimFunVisitor<JamVal> primEvaluator = 
        new PrimFunVisitor<JamVal>() { /* ANONYMOUS CLASS */
        
        private JamVal primFunError(String fn) {
          throw new EvalException("Primitive function `" + fn + "' applied to " + 
                                  arity + " arguments");
        }
        
        private JamCons toJamCons(JamVal val, String fun) {
          if (val instanceof JamCons) return (JamCons) val;
          throw new EvalException("Primitive function `" + fun + "' applied to argument " + val + 
                                  " that is not a JamCons");
        }
        
        public JamVal forFunctionPPrim() {
          if (arity != 1) return primFunError("function?");
          return BoolConstant.toBoolConstant(vals[0] instanceof JamFun);
        }
        
        public JamVal forNumberPPrim() {
          if (arity != 1) return primFunError("number?");
          return BoolConstant.toBoolConstant(vals[0] instanceof IntConstant);
        }
        
        public JamVal forListPPrim() {
          if (arity != 1) return primFunError("list?");
          return BoolConstant.toBoolConstant(vals[0] instanceof JamList);
        }
        
        public JamVal forConsPPrim() {
          if (arity != 1) return primFunError("cons?");
          return BoolConstant.toBoolConstant(vals[0] instanceof JamCons);
        }
        
        public JamVal forEmptyPPrim() {
          if (arity != 1) return primFunError("empty?");
          return BoolConstant.toBoolConstant(vals[0] instanceof JamEmpty);
        }
        
        public JamVal forRefPPrim() {
          if (arity != 1) return primFunError("ref?");
          return BoolConstant.toBoolConstant(vals[0] instanceof JamRef);
        }
        
        public JamVal forConsPrim() {
          if (arity != 2) return primFunError("cons"); 
          if (! (vals[1] instanceof JamList))
            throw new EvalException("Second argument " + vals[1] + " to `cons' is not a JamList");
          return new JamCons(vals[0], (JamList) vals[1]);
        }
        
        public JamVal forArityPrim() { 
          if (arity != 1) return primFunError("arity");
          if (! (vals[0] instanceof JamFun) ) throw new EvalException("arity applied to argument " +
                                                                      vals[0]);
          return ((JamFun) vals[0]).accept(arityEvaluator);
        }
        
        public JamVal forFirstPrim() { return toJamCons(vals[0], "first").first(); }
        public JamVal forRestPrim() { return toJamCons(vals[0], "rest").rest(); }
        
        
        public JamVal forAsBoolPrim() {
          JamVal val = vals[0];
          if (val instanceof BoolConstant) return val;
          else throw new EvalException("The Jam value " + val + " must be of boolean type");
        }
      };
      
      FunVisitor<IntConstant> arityEvaluator = new FunVisitor<IntConstant>() { /* ANONYMOUS CLASS */
        public IntConstant forClosure(Closure jc) { return new IntConstant(jc.arity()); }
        public IntConstant forPrimFun(PrimFun jpf) { return jpf.accept(primArityEvaluator); }
      };
    }
    
    /** Inner class of Evaluator: UnOpEvaluator */
    class UnOpEvaluator implements UnOpVisitor<JamVal> {
      private JamVal val;
      
      UnOpEvaluator(JamVal jv) { val = jv; }
      
      private IntConstant checkInteger(UnOp op) {
        if (val instanceof IntConstant) return (IntConstant) val;
        throw new EvalException("Unary operator `" + op + "' applied to non-integer " + val);
      }
      
      private BoolConstant checkBoolean(UnOp op) {
        if (val instanceof BoolConstant) return (BoolConstant) val;
        throw new EvalException("Unary operator `" + op + "' applied to non-boolean " + val);
      }
      
      private JamRef checkRef(UnOp op) {
        if (val instanceof JamRef) return (JamRef) val;
        throw new EvalException("Unary operator `" + op + "' applied to non-reference" + val);
      }
      public JamVal forDefault(UnOp op) { 
        throw new EvalException(op + " is not a supported unary operation");
      }
      public JamVal forUnOpPlus(UnOpPlus op) { return checkInteger(op); }
      public JamVal forUnOpMinus(UnOpMinus op) { 
        return new IntConstant(- checkInteger(op).value()); 
      }
      public JamVal forOpTilde(OpTilde op) { return checkBoolean(op).not(); }
      public JamVal forOpBang(OpBang op) { return checkRef(op).value(); }
      public JamVal forOpRef(OpRef op) { return new JamRef(val); }
    }
    
    /** Inner class of Evaluator: BinOpEvaluator. */
    class BinOpEvaluator implements BinOpVisitor<JamVal> { 
      private AST arg1, arg2;
      
      BinOpEvaluator(AST a1, AST a2) { arg1 = a1; arg2 = a2; }
      
      private IntConstant evalIntegerArg(AST arg, BinOp b) {
        JamVal val = arg.accept(Evaluator.this);
        if (val instanceof IntConstant) return (IntConstant) val;
        throw new EvalException("Binary operator `" + b + "' applied to non-integer " + val);
      }
      
      private BoolConstant evalBooleanArg(AST arg, BinOp b) {
        JamVal val = arg.accept(Evaluator.this);
        if (val instanceof BoolConstant) return (BoolConstant) val;
        throw new EvalException("Binary operator `" + b + "' applied to non-boolean " + val);
      }
      
      private JamRef evalRefArg(AST arg) {
        JamVal box = arg.accept(Evaluator.this);
        if (box instanceof JamRef) return (JamRef) box;
        throw new EvalException("Binary operator " + OpGets.ONLY + " applied to non-ref " + box);
      }
      
      private JamVal evalArg(AST arg) {
        return arg.accept(Evaluator.this);
      }
      
      public JamVal forDefault(BinOp op) {
        throw new EvalException(op + " is not a supported binary operation");
      }
      
      public JamVal forBinOpPlus(BinOpPlus op) {
        return new IntConstant(evalIntegerArg(arg1,op).value() + evalIntegerArg(arg2,op).value());
      }
      public JamVal forBinOpMinus(BinOpMinus op) {
        return new IntConstant(evalIntegerArg(arg1,op).value() - evalIntegerArg(arg2,op).value());
      }
      
      public JamVal forOpTimes(OpTimes op) {
        return new IntConstant(evalIntegerArg(arg1,op).value() * evalIntegerArg(arg2,op).value());
      }
      
      public JamVal forOpDivide(OpDivide op) {
        int divisor = evalIntegerArg(arg2,op).value();
        if (divisor == 0) throw new EvalException("Attempt to divide by zero");
        return new IntConstant(evalIntegerArg(arg1,op).value() / divisor);
      }
      
      public JamVal forOpEquals(OpEquals op) {
        return BoolConstant.toBoolConstant(arg1.accept(Evaluator.this).equals(arg2.accept(Evaluator.this)));
      }
      
      public JamVal forOpNotEquals(OpNotEquals op) {
        return BoolConstant.toBoolConstant(! arg1.accept(Evaluator.this).equals(arg2.accept(Evaluator.this)));
      }
      
      public JamVal forOpLessThan(OpLessThan op) {
        return BoolConstant.toBoolConstant(evalIntegerArg(arg1,op).value() < evalIntegerArg(arg2,op).value());
      }
      
      public JamVal forOpGreaterThan(OpGreaterThan op) {
        return BoolConstant.toBoolConstant(evalIntegerArg(arg1,op).value() > evalIntegerArg(arg2,op).value());
      }
      
      public JamVal forOpLessThanEquals(OpLessThanEquals op) {
        return BoolConstant.toBoolConstant(evalIntegerArg(arg1,op).value() <= evalIntegerArg(arg2,op).value());
      }
      
      public JamVal forOpGreaterThanEquals(OpGreaterThanEquals op) {
        return BoolConstant.toBoolConstant(evalIntegerArg(arg1,op).value() >= evalIntegerArg(arg2,op).value());
      }
      
      public JamVal forOpAnd(OpAnd op) {
        BoolConstant b1 = evalBooleanArg(arg1,op);
        if (b1 == BoolConstant.FALSE) return BoolConstant.FALSE;
        return evalBooleanArg(arg2,op);
      }
      public JamVal forOpOr(OpOr op) {
        BoolConstant b1 = evalBooleanArg(arg1,op);
        if (b1 == BoolConstant.TRUE) return BoolConstant.TRUE;
        return evalBooleanArg(arg2,op);
      }
      public JamVal forOpGets(OpGets op) { 
        JamRef r = evalRefArg(arg1);
        r.setValue(evalArg(arg2));
        return JamUnit.ONLY;
      }
    }
  }  // end of Evaluator abstract class
  
  /** Inner class of Interpreter: a visitor for evaluating SymASTs derived from the Evaluator class. */
  class SymEvaluator extends Evaluator<VarEnv> implements SymASTVisitor<JamVal> {
    
    public SymEvaluator(VarEnv e) { super(e); }
    
    public SymASTVisitor<JamVal> newEvalVisitor(VarEnv env) { return new SymEvaluator(env); }
    
    public JamVal forVariable(Variable v) { return env.lookup(v); }
    
    public JamVal forMap(Map m) { return new SymClosure(m, this); }   
    
    public JamVal forLet(Let l) {
      /* simple non-recurisve let semantics */
      
      /* Extract binding vars and exps (rhs's) from l */
      Variable[] vars = l.vars();
      SymAST[] exps = l.exps();
      int n = vars.length;
      
      /* construct newEnv for Let body and exps; vars are bound to values of corresponding exps 
       * using newEvalVisitor */
      VarEnv newEnv = env();
      Binding[] bindings = new Binding[n];
      
      for (int i = n-1; i >= 0; i--) {
        bindings[i] = new Binding(vars[i], exps[i].accept(this));  // bind var[i] to exps[i] in this evaluator
        newEnv = newEnv.cons(bindings[i]);          
      }
      
      SymASTVisitor<JamVal> newEvalVisitor = newEvalVisitor(newEnv);
      
      return l.body().accept(newEvalVisitor);
      
    }
    
    public JamVal forLetRec(LetRec l) {
      /* recursive let semantics */
      
      /* Extract binding vars and exps (rhs's) from l */
      Variable[] vars = l.vars();
      SymAST[] exps = l.exps();
      int n = vars.length;
      
      // construct newEnv for Let body and exps; vars are bound to values of corresponding exps using newEvalVisitor
      VarEnv newEnv = env();
      
      Binding[] bindings = new Binding[n];
      for (int i = n-1; i >= 0; i--) {
        bindings[i] = new Binding(vars[i],null);  // bind var[i], setting env to null
        newEnv = newEnv.cons(bindings[i]);          
      }
      
      SymASTVisitor<JamVal> newEvalVisitor = newEvalVisitor(newEnv);
      
      // fix up the dummy values
      for (int i = 0; i < n; i++) 
        bindings[i].setBinding(exps[i].accept(newEvalVisitor));  // modifies newEnv and newEvalVisitor
      
      return l.body().accept(newEvalVisitor);
    }
    
    /*( Abort on encountering tree nodes that are illegal in a SymAST */
    public JamVal forSDPair(SDPair host) { return forDefault(host); }
    public JamVal forSMap(SMap host) { return forDefault(host); }
    public JamVal forSLet(SLet host) { return forDefault(host); }
    public JamVal forSLetRec(SLetRec host) { return forDefault(host); }
    
  }
  
  /** Inner class of Interpreter: a high-level visitor for evaluating SDASTs*/
  class SDEvaluator extends Evaluator<SDEnv> implements SDASTVisitor<JamVal> {
    
    SDEvaluator(SDEnv env) { super(env); }
    
    /*  EvalVisitor methods for evaluating SDASTs. */
    public SDASTVisitor<JamVal> newEvalVisitor(SDEnv env) { return new SDEvaluator(env); }
    public JamVal forSDPair(SDPair p)  { return env.lookup(p); }
    public JamVal forSMap(SMap sm) { return new SDClosure(sm, this); }
    public JamVal forSLet(SLet sl) {
      SDAST[] rhss = sl.rhss();
      int n = rhss.length;
      JamVal[] vals = new JamVal[n];
      for (int i = 0; i < n; i++) vals[i] = rhss[i].accept(this);
      SDEnv newEnv = env().cons(vals);
      return sl.body().accept(newEvalVisitor(newEnv));
    }
    public JamVal forSLetRec(SLetRec slr) {
      SDAST[] rhss = slr.rhss();
      int n = rhss.length;
      JamVal[] vals = new JamVal[n];
      SDEnv newEnv = env().cons(vals);
      SDASTVisitor<JamVal> bodyVisitor = newEvalVisitor(newEnv);
      for (int i = 0; i < n; i++) vals[i] = slr.rhss()[i].accept(bodyVisitor);
      return slr.body().accept(bodyVisitor);
    } 
    
    /* Methods that are never invoked in the evaluation of well-formed SymASTs */
    public JamVal forVariable(Variable host) { return forDefault(host); }
    public JamVal forMap(Map host) { return forDefault(host); }
    public JamVal forLet(Let host) { return forDefault(host); }
    public JamVal forLetRec(LetRec host) { return forDefault(host); }
  }

  
  /* Concrete heap based interpreter for SDASTs that runs with an explicit heap and two stacks: for and envs.  
   * An env is a linked list of activation records in the heap, patterned after the Algol 60 runtime. */
  
  /**  Overview of RAM Machine */
  /* Concrete record representation of run-time data in the heap:
   * 
   * Every record is a sequence of word-long (Java int) fields separated by semicolons; the pointer fields are prefixed by the word
   * "heapAddr" and the int value fields are preceded by the word "int"
 
   * There are 15 negative pseudo-pointer values that can be uses records of ints to represent JamVals
   *   EMPTY  = -1
   *   UNIT  = -2
   *   TRUE  = -3
   *   FALSE = -4
   *   NUMBERP   = -5;
   *   FUNCTIONP = -6;
   *   LISTP     = -7;
   *   CONSP     = -8;
   *   EMPTYP    = -9;
   *   REFP      = -10
   *   ARITY     = -11;
   *   CONSFN    = -12;
   *   FIRST     = -13;
   *   REST      = -14;
   *   ASBOOL    = -15
   * 
   *   FORWARD   = Integer.MIN_VALUE;  // unused
   * 
   *   TODO: (i) introduce ILLEGAL as a psuedo-pointer value after FALSE but before NUMBERP and (ii) check for it at runtime
   * 
   * All other legal heapAddr values are non-negative indices in the heap array.  The first word of each record in the
   * heap array is one of the following five tags:
   * 
   * INT  = 1;      int value
   * CONS = 2;      heapAddr first, heapAddr rest
   * REF  = 3;      heapAddr contents
   * CLOSURE = 4;   int codeIndex; heapAddr env
   * ACTRECORD = 5; heapAddr {environment}; numbindings; heapAddr[numbindings] bindings
   * 
   * A heapAddr either refers to a Jam value or a Jam environment.  One value, namely the empty list (EMPTY), is common
   * to both Jam values and Jam environments.
   * Pseudo-pointer values and pointers to all of the record variants except ACTRECORD can appear in a Jam value.  
   * An environment is a linked list of ACTRECORDs terminated by EMPTY.  Environments only appear in the stack and
   * as the {environment} field of an ACTRECORD.
   * NOTE: For ACTRECORD, using the tag value 5 + numbindings (which may be zero) might be more efficient; it requires
   * one less memory cell and fewer memory reads and writes.
   * 
   * The SDEvaluator assumes that;
   * - input program has been converted to static distance coordinate (SD) form;
   * - PrimFun and UnOp/BinOp objects in code are unique;
   * - empty, true, false, unit, and primfn values are epresented by pseudo-indices;
   * - all intermediate results (except envs) that persist through next allocation operation are stored in heap or temps
   * - env pointers of pending computations are stored in env stack; activation records are stored in the heap.
   * - variables are referenced using static distance coordinates. 
   * Hence, == can be used to compare PrimFun and Op tokens, and HeapPtrs that represent Jam bool values.
   * 
   * SDEvaluators always return the type HeapPtr; all temporaries are stored in the temps stack.  The dynamic chain
   * of pending environments is stored in the regular stack.  NOTE: the dynamic links could be stored in activation 
   * records (as in the classic Algol 60 stack run-time) which may be more efficient.  It is certainly more realistic.
   * 
   * Environments consist of linked lists of activation records stored in the heap.  An environment is represented by a 
   * pointer to its first activation record in the heap or the pseudo-pointer code for EMPTY if it is empty.  The pointer
   * to the current environment resides in the top cell of the stack, which is cell 0 at the top level.  NOTE: the 
   * execution of each forXXX visitor method leaves the stack unchanged!  In other words, the stackPtr must be saved and
   * restored by any such method that pushed anything on the stack.
   * 
   * In each activation record, the second word (offset 1) points to the lexically enclosing activation record.  The 
   * third word (offsets 2) is the number N of new bindings in the record.  The remaining N cells hold pseudo-pointers
   * representing special JamVals or pointers (indices) to heap records representing JamVals.
   * 
   * The returned results (pointers to Heap records) are NOT necessarily reachable.  They must be stored in the
   * stack or heap before subsequent allocation-driven GC can occur.
   */
  
  /* Data representations in the RAM Machine */
  
  static final int EMPTY  = -1;
  static final int UNIT  = -2;
  static final int TRUE  = -3;
  static final int FALSE = -4;
  
  /* Data representations for primitive function values */
  /* <prim>  ::= number? | function? | list? | null? | cons? | ref? | arity | cons | first | rest */
  
  static final int NUMBERP   = -5;
  static final int FUNCTIONP = -6;
  static final int LISTP     = -7;
  static final int CONSP     = -8;
  static final int EMPTYP    = -9;
  static final int REFP      = -10;
  static final int ARITY     = -11;
  static final int CONSFN    = -12;
  static final int FIRST     = -13;
  static final int REST      = -14;
  static final int ASBOOL    = -15;
  
  /** Node tag values */
  static final int FORWARD   = 0;                 // fields: heapAddr {forwarding ptr to new space}
  static final int INT       = 1;                 // fields: int {value}
  static final int CONS      = 2;                 // fields: heapAddr {first}, heapAddr {rest}
  static final int REF       = 3;                 // fields: heapAddr {contents}
  static final int CLOSURE   = 4;                 // fields: int {code index}; heapAddr {environment ptr}
  static final int ACTRECORD = 5;                 // fields: heapAddr{environment ptr}, int {number of bindings}; 
                                                  //         heapAddr[number of Bindings] {bindings}
  
  
  /** Inner class of Interpreter: Stack, which is the class supporting the two run-time stacks in RAM SD evaluation:
    * envs and temps.  */ 
  class Stack {
    
    private final int[] regs;
    private int stackPtr;

    Stack(int size) {
      stackPtr = 0;
      regs = new int[size];
    }
    int size() { return stackPtr; }
  
    int top() { 
      if (stackPtr <= 0) throw new EvalException("Attempt to access top of empty stack");
      return regs[(stackPtr-1)]; 
    }
    int get(int i) { return regs[i]; }
    void set(int i, int v) { regs[i] = v; }
    int getStackPtr() { return stackPtr; }
    
    int pop() { 
      if (stackPtr <= 0) throw new EvalException("Stack underflow");
      int top = top();
      stackPtr--;
      regs[stackPtr] = 0; // clear contents of popped cell
      return top;
    }
    
    /** push i onto the stack and return its offset+1, the resulting stack size.  This value is not currently used. */
    int push(int i) {
//      System.err.println("pushing " + i + " on " + this);
      if (stackPtr >= STACKSIZE) throw new EvalException("Stack overflow");
      regs[stackPtr] = i; 
      stackPtr++;
      return stackPtr;
    }
    
    public String toString() {
      Object[] oRegs = new Object[stackPtr];
      for (int i = 0; i < stackPtr; i++) oRegs[i] = regs[i];
      return "Stack " + super.toString() + " with " + stackPtr + " elements [" +  ToString.toString(oRegs, ",", stackPtr) + "]";
    } 
  }
  
  /** Inner class of Interpreter supporting an explicit heap for RAM SD evaluation.  The enviroment stack must be allocated 
    * before the Heap is allocated. */
  class Heap {
    
    /* Instance constants that reference a specific instance in the heap. */
    private final HeapPtr EMPTYPtr = new HeapPtr(EMPTY);
    private final HeapPtr UNITPtr = new HeapPtr(UNIT);
    private final HeapPtr TRUEPtr = new HeapPtr(TRUE);
    private final HeapPtr FALSEPtr = new HeapPtr(FALSE);
    
    private int[] cells, newCells;
    private int freePtr;
    private final int size;
    
    private Stack envs = new Stack(STACKSIZE);
    private Stack temps = new Stack(TEMPSSIZE);
    
    Heap(int i) {
//      System.err.println("Creating NEW HEAP");
      size = i;
      if (size < 1) throw new EvalException("Heap size must be at least 1");
      freePtr = 0;
      cells = new int[size];
    }
    
    int size() { return size; }
    int freePtr() { return freePtr; }
    int[] getCells() { return cells; }
    int getStackSize() { return envs.size(); }
    int getTempsSize() { return temps.size(); }
    
    /* Create a bare RamSDEvaluator (stack must already exist) initializing stack and the empty environment. temps?*/
    RamSDEvaluator newRamSDEvaluator() { return new RamSDEvaluator(); }
    
    /* Allocate n words forcing a garbage collection if necessary. */
    int alloc(int n) {
      /* cells.length is the min illegal index, freePtr+n is one more than the last required index. */
      if (freePtr+n > cells.length) {
//        System.err.println(freePtr + " cells in use");
        gc();
        if (freePtr+n > cells.length) 
          throw new EvalException("Out of heap memory");
      }      
      int base = freePtr;
      freePtr += n;
//      System.err.println("After allocation, freePtr = " + freePtr);
      return base;
    }
    
    private void assertFalse() { throw new RuntimeException("Attempted to perform GC"); }
    
    private void gc() { /* STUB for extra credit */ assertFalse(); }
    
  
    public String toString() {
      Object[] oCells = new Object[freePtr];
      for (int i = 0; i < freePtr; i++) oCells[i] = cells[i];
      return "Heap has " + freePtr + " elements\n" + ToString.toString(oCells, ", ", freePtr); 
    } 
    
    /** Heap utility code */
    static final int ROW_WIDTH = 8;
    static final int ITEM_WIDTH = 10;
    
    public String dump(String heading, int[] cells, int n) {
      StringBuffer result = new StringBuffer(heading);
      result.append(" (" + n + " elements)");
      for (int i = 0; i < n;) {
        // inner loop increments i;
        int j = i + ROW_WIDTH;
        if (j > n) j = n;
        result.append("\n");
        for (;i < j; i++) {
          String next = Integer.toString(cells[i]);
          for (int k = 0; k < ITEM_WIDTH - next.length(); k++) result.append(" ");
          result.append(next);
        }
      }
      return result.toString();
    }
    
    /** Convert low-level JamVal representation to corresponding JamVal */
    JamVal decode(int addr) {
//      System.err.println("Decoding heap address/pseudo-address " + addr);
      if (addr < 0) { // addr is pseudo-pointer
//        System.err.println("Switching on " + addr + " in decode");
        switch (addr) {  // Java may not compile this switch statement well since it is descending from -1
          case EMPTY:  return JamEmpty.ONLY;
          case UNIT:  return JamUnit.ONLY;
          case TRUE:  return BoolConstant.TRUE;
          case FALSE: return BoolConstant.FALSE;
          
          /* Primitive function objects */
          case NUMBERP:   return NumberPPrim.ONLY;
          case FUNCTIONP: return FunctionPPrim.ONLY;
          case LISTP:     return ListPPrim.ONLY;
          case CONSP:     return ConsPPrim.ONLY;
          case EMPTYP:    return EmptyPPrim.ONLY;
          case REFP:      return RefPPrim.ONLY;
          case ARITY:     return ArityPrim.ONLY;
          case CONSFN:    return ConsPrim.ONLY;
          case FIRST:     return FirstPrim.ONLY;
          case REST:      return RestPrim.ONLY;
          default: throw new EvalException("Illegal pseudo-pointer code " + addr);
        }
      }
      
      /* addr >=0 */
      if (addr >= heap.size()) throw new EvalException("Heap pointer " + addr + " exceeds heap size (" + heap.size() + ")");
      
      switch (heap.cells[addr]) {
        case INT:  return new IntConstant(heap.cells[addr+1]);
        case CONS: 
        { JamVal rest = decode(heap.cells[addr + 2]);
          if (rest instanceof JamList) return new JamCons(decode(heap.cells[addr + 1]), (JamList) decode(heap.cells[addr + 2]));
          throw new EvalException("Second argument to cons = " + rest + ", which is not a JamList");
        }
        case REF:  return new JamRef(decode(heap.cells[addr+1])); 
        case CLOSURE: 
//        System.err.println("Decoding closure at heap address " + addr + " map offset is " + heap.cells[addr+1]);
          return new SDClosure((SMap) sConverter.getCode(heap.cells[addr+1]), null);  // evaluator omitted
        case ACTRECORD: throw new
          EvalException("Attempt to convert heap addr pointing to an ACTRECORD to a JamVal\nAs an env pointer, it is: " + envDecode(addr));
        default:   throw new EvalException("Illegal heap record tag " + heap.cells[addr] + " encountered within a JamVal representation");
      }
    }
    
    /** Decodes the environment identified by heap address addr. */
    ArrayList<ArrayList<JamVal>> envDecode(int addr) {
      return envDecodeHelp(addr, new ArrayList<ArrayList<JamVal>>(), 0);
    }
    
    /** Appends the environment identified by heap address addr to the environment (an ArrayList<JamVal>) in result. */
    ArrayList<ArrayList<JamVal>> envDecodeHelp(int addr, ArrayList<ArrayList<JamVal>> result, int ct) {
      if (ct > DEPTH_BOUND) throw new EvalException("attempt decode an env blew up at index " + addr);
      if (addr == EMPTY) return result;
      if (heap.cells[addr] != ACTRECORD) throw new 
        EvalException("Attempt to decode a heap record of type " + heap.cells[addr] + " as activation record");
      int numVars = heap.cells[addr+2];
      int[] valPtrs =  (numVars > 0) ? Arrays.copyOfRange(heap.cells, addr+3, addr+numVars+3): new int[]{};
      ArrayList<JamVal> boundVals = new ArrayList<JamVal>() {{ for (int p : valPtrs) add(decode(p)); }};
//    System.err.println("in **envDecodeHelp**, numVars = " + numVars + " boundVals = " + boundVals);
      int envRestPtr = heap.cells[addr+1];
      result.add(boundVals);
      return envDecodeHelp(envRestPtr, result, ct++);                
    }
    
    /** Allocates val as a new int value in the heap and returns val. */
    int newInt(int val) {
      int base = heap.alloc(2);
      heap.cells[base]   = INT;
//    System.err.println("heap[" + base + "] = " + INT + " [INT]");
      heap.cells[base+1] = val;
//    System.err.println("heap[" + (base+1) + "] = " + val);                    
      return base;
    }
    
    /** Returns the pseudo-pointer (an int) corresponding to b. Does no heap allocation. */
    int newBool(boolean b) { return b ? TRUE : FALSE; }
    
    /** Allocates a new Cons node in the heap and returns a pointer (index) to it.  Assumes that the unallocated heap
      * has been zeroed. */
    int newCons() {
      int base = heap.alloc(3);
      heap.cells[base]   = CONS;
//    System.err.println("heap[" + base + "] = " + CONS + " [CONS]");
      return base;
    }
    int getConsFirst(int addr) {
      if (heap.cells[addr] != CONS) throw new 
        EvalException("location `" + addr + "' misinterpreted as cons");
      return heap.cells[addr+1];
    }
    int getConsRest(int addr) {
      if (heap.cells[addr] != CONS) throw new 
        EvalException("location `" + addr + "' misinterpreted as cons");
      return heap.cells[addr+2];
    }
    void setConsFirst(int addr, int f) {
      if (heap.cells[addr] != CONS) throw new 
        EvalException("location `" + addr + "' misinterpreted as cons");
      heap.cells[addr+1] = f;
//    System.err.println("heap[" + (addr+1) + "] = " + f);
    }
    
    void setConsRest(int addr, int r) {
      if (heap.cells[addr] != CONS) throw new 
        EvalException("location `" + addr + "' misinterpreted as cons");
      heap.cells[addr+2] = r;
//    System.err.println("heap[" + (addr+2) + "] = " + r);
    }
    
    /** Allocates a new Ref node in the heap and returns a pointer (index) to it.  Assumes that the unallocated heap
      * has been zeroed. */
    int newRef() {
      int base = heap.alloc(2);
      heap.cells[base]   = REF;
//    System.err.println("heap[" + base + "] = " + REF + " [REF]");
      return base;
    }
    
    /** Allocates a new Closure node in the heap and returns a pointer (index) to it.  Assumes that the unallocated heap
      * has been zeroed. */
    int newClosure(int codeIndex) {
      int base = heap.alloc(3);
      heap.cells[base]   = CLOSURE;
//    System.err.println("heap[" + base + "] = " + CLOSURE + " [CLOSURE]");
      heap.cells[base+1] = codeIndex;
//    System.err.println("heap[" + (base+1) + "] = " + codeIndex);
//    System.err.println("Allocating closure with code index " + codeIndex + " at heap location " + base);
      return base;
    }
   
    /* Determines if the pseudo-object or heap object for addr has the low-level type specified by tag */ 
    boolean instanceOf(int addr, int tag) {
      if (addr < 0) return tag == addr;  // pseudo-indices are tag values
      return heap.cells[addr] == tag; 
    }
    
    /** Determines if the addr is pseudo-pointer to a primitive function */
    boolean isPrimFun(int addr) { return (ASBOOL <= addr) && (addr <= NUMBERP); }
    
    /*** Low-level operations on Activation nodes. These methods are all very short ***/
    
    /** Allocates a new Activation node accommodating the specified number of bindings and returns the index of the
      * node.  Assumes that the unallocated heap has been zeroed. */
    int newActRecord(int numBindings) { return EMPTY; /* STUB */ }
    
    /* Each operation that directly accesses an existing heap node dynamically confirms that the accessed heap node has
     * the specified type.  These checks are unnecessary (and costly?) in the absence of bugs but they prudently support debugging. */
    /** sets the env ptr [static link] within an Activation node [in the heap at address addr] to the value env */
    void setActEnv(int addr, int env) { return; /* STUB */ }
    
    /** Sets the specified Activation variable (slot) within an Activation node at the specified address (index) 
      * using a wrapped low-level Jam value */
    void setActVar(int addr, int offset, HeapPtr val) { return; /* STUB */ }
    
    /** sets the specified Activation variable (slot) within an Activation node at the specifed address (index) 
      * using an int index value rather than HeapPtr (which wraps indexes [pointers} into the heap. */
    void setActVar(int addr, int offset, int val) { return; /* STUB */ } 
    
    /** gets the specified Activation variable (argument) at the specified address (index) within an Activation node 
      * as an int index value. */
    int getActVar(int addr, int offset) { return EMPTY; /* STUB */ }
    
    /** gets the env pointer (index) within an Activation node at the specified address (index) as an int index value. */
    int getActEnv(int addr) { return EMPTY; /* STUB */ }
    
    /** Checks if Activation record at specified address (index) accommodates the specified offset. */
    void checkOffset(int addr, int offset) { return; /* STUB */ }
    
    /** Inner class of Heap: instances point to RAM SD values in the heap.  This class simply wraps ints used to index 
      * the heap array.  This data representation is technically unnecessary and adds some overhead, but it makes 
      * it easier to detect bugs in code manipulating heap indices.
      */ 
    class HeapPtr {
      
      private int addr; // Either a negative pseudo-index or an index in the Heap array
      
      HeapPtr(int a) { addr = a; }
      
      int getAddr() { return addr; }
      
      /** Determines if this is a instance of a node with the specified tag. Applied to the headers of heap records. */
      boolean instanceOf(int tag) {
        return (addr >= 0) && Heap.this.instanceOf(addr, tag);  // (addr >= 0) rejects pseudo-indices
      }
      
      int toInt() {
        if (! instanceOf(INT)) throw new EvalException("location `" + addr + "' misinterpreted as number");
        return cells[addr+1];
      }
      
      int getRefVal() {
        if (! heap.instanceOf(addr, REF)) throw new EvalException("location `" + addr + "' misinterpreted as reference record");
        return heap.cells[addr+1];
      }
      
      void setRef(int val) {
        if (! heap.instanceOf(addr, REF)) throw new EvalException("location `" + addr + "' misinterpreted as reference record");
//      System.err.println("heap.cells[" + (addr + 1) + "] = " + val);
        heap.cells[addr+1] = val;
      }
      
      int getClosureEnv() {
        if (! heap.instanceOf(addr, CLOSURE)) throw new EvalException("location `" + addr + "' misinterpreted as closure record");
        return heap.cells[addr+2];
      }
      
      void setClosureEnv(int env) {
        if (! heap.instanceOf(addr, CLOSURE)) throw new EvalException("location `" + addr + "' misinterpreted as closure record");
//      System.err.println("heap.cells[" + (addr + 2) + "] = " + env);
        heap.cells[addr+2] = env;
      }
      
      int getClosureCode() {
        if (heap.cells[addr] != CLOSURE) throw new EvalException("location `"
                                                                   + addr + "' misinterpreted as closure record");
        return heap.cells[addr+1];
      }
      
      public boolean equals(Object other) {
        if (!(other instanceof HeapPtr)) return false;
        HeapPtr ohp = (HeapPtr) other;
        return equalHeapJamVal(addr, ohp.addr);
      }
      
      boolean equalHeapJamVal(int addr1, int addr2) { return false; /* STUB */ }
      
      public JamVal decode() { return Heap.this.decode(addr); }
      
      public String toString() { return "Heap address: " + addr + " with contents " + decode(); }
    }
    
    /* Inner class of Interpreter; A visitor that implements RAM interpreter for SDAST code; does NOT assume code conforms to CPS */
    class RamSDEvaluator implements SDEvalVisitor {
      
      /* Assumes that;
       * - input program has been converted to SD form;
       * - PrimFun and Op objects are unique;
       * - empty, true, false, unit are epresented by pseudo-indices EMPTY, TRUE, FALSE, UNIT;
       * - all intermediate results that persist through next allocation operation are stored in the heap or stack;
       * - variables are referenced using static distance coordinates. 
       * Hence, == can be used to compare PrimFuns, OpTokens, and HeapPtrs that represent Jam bool values.
       * 
       * Evaluators always return the type HeapPtr; all temporaries are either stored in the heap or pushed onto the 
       * stack.  Activation records are represented by int pointers into the heap. The current activation record resides
       * in the top cell of the stack, which is cell 0 at the top level.  NOTE: the execution of each forXXX visitor
       * method leaves the stack unchanged!  In other words, the stackPtr must be saved and restored by any such method
       * that pushed anything on the stack.
       * 
       * Environment chains are represented by activation records in the heap. The second word (offset 1) points to the 
       * lexically enclosing activation record.  The third word (offsets 2) is the number N of new bindings in the 
       * record.  The remaining N cells hold pseudo-pointers representing special JamVals or pointers (indices) to heap
       * records representing JamVals.
       * 
       * The returned results (pointers to Heap records) are NOT necessarily reachable.  They must be stored in the
       * stack or heap before subsequent allocation-driven GC can occur.
       */
      
      /* Pushes env on the stack to become the new current environment. ONLY called from newVisitor to perform
       * recursive evaluation. */
      private RamSDEvaluator(int env) { envs.push(env); }
      
      /** Clears the stack and copies the empty list pseudo-index to stack slot 0 and makes it the initial env pointer. 
        * Used at top-level.*/
      public RamSDEvaluator() {
        /* stack and temps have already been initialized to "empty" state in Interpreter */
        envs.push(EMPTY);  // push the empty environment on the stack 
      }
      
      /** Gets the valule of the "variable" designated by p in env */
      private HeapPtr lookup(SDPair p, int env) {
//      System.err.println("Looking up " + p + " in env " + envDecode(env));
        int k = p.dist();
        for (int i = 0; i < k; i++) env = getActEnv(env);  // chase up the static chain to get the specified activation record
//      System.err.println("In lookup, using env record " + k + " offset = " + p.offset());
        return new HeapPtr(getActVar(env, p.offset()));   // return the contents of the specfied heap cell
      }
      
      /** Returns the value of the top cell in the stack */
      public int env() { return envs.top(); }   // Assumes no stack leaks
      
      public UnOpVisitor newUnOpVisitor;
      
      /** Recursively creates a new visitor pushing envPtr on top of the env stack, which is used as the environment 
        * pointer for the new evaluation. The caller is responsible for deallocating the envPtr.  */
      public RamSDEvaluator newVisitor(int envPtr) {
        if (! instanceOf(envPtr, ACTRECORD)) throw new 
          EvalException("Attempted to push " + envPtr + " on env stack with tag" + heap.cells[envPtr]);
//      System.err.println("Starting newVisitor; stack.size() = " + stack.size()); 
        return new RamSDEvaluator(envPtr);
      }
      
      /** Evaluate the expressions in the array exps and push the results on the temps Stack. */
      public void evalExps(SDAST[] exps) { 
//      System.err.println("Evaluating exps " + Arrays.toString(exps));
        for (int i = 0; i < exps.length; i++) {
          int addr = exps[i].accept(this).getAddr();  /* may trigger GC */
          temps.push(addr);
//        System.err.println("Pushed " + addr + " as argument on temps stack");
        }
      }
      
      public void numberOfArgumentsError(PrimFun fn, int num) { throw new 
        EvalException("Wrong number of arguments (" + num + ") passed to primitive function " + fn);
      }
      
      public HeapPtr forDefault(AST a) { 
        throw new EvalException(a + " is not in the domain of the visitor " + getClass());
      }
      
      public HeapPtr forBoolConstant(BoolConstant b) { return null; /* STUB */ }
      public HeapPtr forIntConstant(IntConstant i) { return null; /* STUB */ }
      public HeapPtr forEmptyConstant(EmptyConstant n) { return null; /* STUB */ }
      
      public HeapPtr forVariable(Variable v) { return forDefault(v); }
      public HeapPtr forSDPair(SDPair p)  { return null; /* STUB */ }
      
      /** The integers in [-4, -1] are the pseudo-indices representing the JamVals null, true, false, and unit. This 
        * function maps the primitive functions (in the order listed in PrimFunVisitor) to the integers in [-15, -5]. */
      public HeapPtr forPrimFun(PrimFun f) { return null; /* STUB */ }  
      
      public HeapPtr forUnOpApp(UnOpApp u) { return null; /* STUB */ }    
      public HeapPtr forBinOpApp(BinOpApp b) { return null; /* STUB */ } 
      public HeapPtr forApp(App a) { return null; /* STUB */ } 
      public HeapPtr forMap(Map m) { return forDefault(m); }
      public HeapPtr forSMap(SMap sm) { return null; /* STUB */ }
      public HeapPtr forIf(If i) { return null; /* STUB */ }
      public HeapPtr forBlock(Block b) { return null; /* STUB */ }
      public HeapPtr forLet(Let l) { return forDefault(l); }
      public HeapPtr forSLet(SLet sl) { return null; /* STUB */ } 
      public HeapPtr forLetRec(LetRec host) { return forDefault(host); }
      public HeapPtr forSLetRec(SLetRec slr) { return null; /* STUB */ } 
      
      /** Applies the closure at location c in the heap to the arguments obtained by evaluating the expressions in the 
        * args array.  Must manage temps and stack carefully. */
      private HeapPtr applyClosure(HeapPtr c, SDAST[] args) { return null; /* STUB */ } 
    }
  }
}

