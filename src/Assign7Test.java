import java.util.StringTokenizer;
import junit.framework.TestCase;
import java.io.*;

/** Testing framework for Assignment 7 Jam **/
public class Assign7Test extends TestCase {
   protected int defaultSize = 50000;

  public Assign7Test (String name) {
    super(name);
  }
  
  private void evalCheck(String name, String answer, String program) {
     evalCheck(name,answer,program, defaultSize);
  }
  private void evalCheck(String name, String answer, String program, int hs) {
      Interpreter interp = new Interpreter(new StringReader(program), hs);
      assertEquals("by-value-value " + name, answer, interp.eval().toString());
  }

  private void cpsEvalCheck(String name, String answer, String program, int hs) {
      Interpreter interp = new Interpreter(new StringReader(program), hs);
      assertEquals("by-value-value " + name, answer, interp.cpsEval().toString());
  }
  
  /** Tests (high-level) SD evaluation */
  private void SDEvalCheck(String name, String answer, String program) {
      Interpreter interp = new Interpreter(new StringReader(program));
      JamVal result = interp.SDEval();
      System.err.println("SDEval result = " + result);
      assertEquals("by-value-value " + name, answer, interp.SDEval().toString());
  }
  
  private void ramSDEvalCheck(String name, String answer, String program, int hs) {
    System.out.printf("%n----: %.7s ----%n", name);
    Interpreter interp = new Interpreter(new StringReader(program), hs);
    
    int[] heap0 = (int[])interp.getMemory().clone(); //shallow copy works here
    
    assertEquals("by-value-value " + name, answer, interp.ramSDEval().toString());
    System.err.println("equality check complete");
    int[] heap1 = (int[])interp.getMemory().clone();
    int count = 0;
    for (int i = 0; i < heap0.length; i++) {
      if (heap0[i] != heap1[i]) { count++; }
    }
    System.err.printf("memory size [%d] : %.7s%n", count, name);
  }

  private void ramSDCpsEvalCheck(String name, String answer, String program, int hs) {
    System.out.printf("%n----: %.7s ----%n", name);
    Interpreter interp = new Interpreter(new StringReader(program), hs);
    
    int[] heap0 = (int[])interp.getMemory().clone(); //shallow copy works here
    
    assertEquals("by-value-value " + name, answer, interp.ramSDCpsEval().toString());
    System.err.println("equality check complete");
    int[] heap1 = (int[])interp.getMemory().clone();
    int count = 0;
    for (int i = 0; i < heap0.length; i++) {
      if (heap0[i] != heap1[i]) { count++; }
    }
    System.err.printf("memory size [%d] : %.7s%n", count, name);
  }

  private void allCheck(String name, String answer, String program) {
     allCheck(name, answer, program, defaultSize);
  }

  // All tests involving cps conversion and ramSD (low=level SD) interpretation are commented out
  private void allCheck(String name, String answer, String program, int hs) {
    evalCheck(name, answer, program, hs);
    System.err.println("eagerCheckComplete");
//    cpsEvalCheck(name, answer, program, hs);
//    System.err.println("cpsCheckComplete");
    SDEvalCheck(name, answer, program);
    System.err.println("SDEagerCheckComplete");
//    SDCpsCheck(name, answer, program, hs);
//    System.err.println("SDCpsheckComplete");
//    GCSDCpsCheck(name, answer, program, hs/3);
  }

  private void unshadowConvert(String name, String answer, String program) {
   unshadowConvert(name, answer, program, defaultSize);
  }

  private void unshadowConvert(String name, String answer, String program, int hs) {
      Interpreter interp = new Interpreter(new StringReader(program), hs);

      String result = interp.unshadow().toString();
      assertEquals("shadowCheck " + name, answer, result);
  }

  private void cpsConvert(String name, String answer, String program) { 
     cpsConvert(name,answer, program, defaultSize);
  } 

  private void cpsConvert(String name, String answer, String program, int hs) {
      Interpreter interp = new Interpreter(new StringReader(program), hs);

      String result = interp.convertToCPS().toString();
      assertEquals("shadowCheck " + name, answer, result);
  }

  private void sdConvert(String name, String answer, String program) {
      Interpreter interp = new Interpreter(new StringReader(program));

      String result = interp.convertToSD().toString();
      assertEquals("shadowCheck " + name, answer, result);
  }
    
  public void testBadLetrec() {
    try {
      String output = "!";
      String input = "letrec x:=4; in x";
      allCheck("badLetrec", output, input );

         fail("badLetrec did not throw ParseException exception");
      } catch (ParseException e) {   
         //e.printStackTrace();
      
    } catch (Exception e) {
      fail("badLetrec threw " + e);
    }
  } //end of func
  
  public void testParseAndOutputLet() {
    
    String answer = "let x:1 := 2; in ((let x:2 := 3; in x:2) + x:1)";
    String program = "let x := 2; in (let x := 3; in x) + x";
    
    Interpreter interp = new Interpreter(new StringReader(program));
    assertEquals("ParseAndOutputOnly", answer, interp.getUSProg());
  }
 
  public void testBadLet() {
    try {
      String output = "!";
      String input = "let x:= map z to y(z);\n             y:= map z to x(z); in x(5)";
      allCheck("badLet", output, input );

         fail("badLet did not throw SyntaxException exception");
      } catch (SyntaxException e) {   
         //e.printStackTrace();
      
    } catch (Exception e) {
      fail("badLet threw " + e);
    }
  } //end of func
  
  public void testTrivialProg() {
    try {
      String output = "()";
      String input = "let x := empty; in x";
      allCheck("append", output, input);

    } catch (Exception e) {
      e.printStackTrace();
      fail("trivial threw " + e);
    }
  } //end of func
 
  public void testAppend() {
    try {
      String output = "(1 2 3 1 2 3)";
      String input = "letrec append := map x,y to if x = empty then y else cons(first(x), append(rest\n(x), y));" +
                     "in let s := cons(1,cons(2,cons(3,empty))); in append(s,s)";
      allCheck("append", output, input);

    } catch (Exception e) {
      e.printStackTrace();
      fail("append threw " + e);
    }
  } //end of func
  

  public void testBigFib() {
    System.err.println("Starting testBigFib in OldAssign7Test");
    try {
      String output = "((0 1) (1 1) (2 2) (3 3) (4 5) (5 8) (6 13) (7 21) (8 34) (9 55) (10 89) (11 144) (12 233) (13 377) (14 610) (15 987) (16 1597) (17 2584) (18 4181) (19 6765) (20 10946)"
        + " (21 17711) (22 28657) (23 46368) (24 75025) (25 121393))"; 
//      (26 196418) (27 317811) (28 514229) (29 832040) (30 1346269) (31 2178309) (32 3524578) (33 5702887) (34 9227465) (35 14930352))";
//      + " (36 24157817) (37 39088169) (38 63245986) (39 102334155) (40 165580141) (41 267914296) (42 433494437) (43 701408733) (44 1134903170) (45 1836311903))";
      String input = "letrec " +
                     "  fibhelp := map k,fn,fnm1 to if k = 0 then fn else fibhelp(k - 1, fn + fnm1, fn);" +
                     "     pair := map x,y to cons(x, cons(y, empty));" +
                     "in let ffib := map n to if n = 0 then 1 else fibhelp(n - 1, 1, 1);" +
                     "   in letrec fibs :=  map k,l to if 0 <= k then fibs(k - 1, cons(pair(k,ffib(k)), l)) else l; " +
                     "      in fibs(25, empty)";
      allCheck("bigfib", output, input);

    } catch (Exception e) {
        fail("bigfib threw " + e);
    }
  } //end of func
  
   public void testSieve() {

        try {
            String output = "(3 5 7 11 13 17 19 23)"; 
            String input = "letrec susp? := map l to cons?(l) & function?(first(l)); " + 
                           "    makeSusp := map f to cons(f, empty); " +
                                     "fo := map prom to if susp?(prom) then (first(prom))() else prom; " +
                             " mapStream := map f,l to let fol := fo(l); " +
                           "                           in if (fol = empty) then empty " +
                           "                              else cons(f(first(fol)), makeSusp(map  to mapStream(f, rest(fol)))); " +
                           "      filter := map p,l to let fol := fo(l); " +
                           "                           in if (fol = empty) then empty " +
                           "                              else if p(first(fol)) then filter(p, rest(fol)) " +
                           "                              else cons(first(fol), makeSusp(map  to filter(p, rest(fol)))); " +   
                           "     divides := map a,b to (((b / a) * a) = b); " +
                           "     initSeg := map l,n to if (n <= 0) then empty " + 
                           "                           else let fol := fo(l); " +
                           "                                in cons(first(fol), initSeg(rest(fol), n-1)); " +
                           "      primes := map l to let fol := fo(l);  " +
                           "                         in cons(first(fol), makeSusp(map  to primes(filter(map x to divides(first(fol), x), rest(fol))))); " +
                           "     oddNums := map  to cons(3, makeSusp(map  to mapStream(map i to (i + 2), oddNums()))); " +
                           "in initSeg(primes(oddNums()), 8)";
            allCheck("sieve", output, input);
        } catch (VirtualMachineError|Exception e) {
            e.printStackTrace(System.err);
            fail("sieve threw " + e);
        }
    } //end of func
}