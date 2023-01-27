//////////////////////////////////////////////////////////////////////
//
// First-Order Logic Package (Test out theorem provers)
//
// Class:  TestKb
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   12/2/04
//
// TODO:
// -----
//
//////////////////////////////////////////////////////////////////////

package logic.kb.fol;

import java.io.*;
import java.util.*;
import logic.kb.*;

public class TestInference3 {

    public static final int CL_WIDTH = 5;
    public static final int JTP_SEARCH_DEPTH = 25;
    public static final int MAX_RES = 100;

    public static int AMAX = 50; // Read from command line
    public static long _lTime;

    public static void ResetTimer() {
	_lTime = System.currentTimeMillis();
    }

    // Get the elapsed time since resetting the timer
    public static long GetElapsedTime() {
	return System.currentTimeMillis() - _lTime;
    }
    
    public static void main(String args[]) {

	if (args.length != 1) {
	    System.out.println("Requires 1 size argument.");
	    System.exit(1);
	}
	AMAX = (new Integer(args[0])).intValue();

	//System.out.println("\n\n--------------------\nTest #1\n--------------------");
	//Test1(new CachingKb(new ClauseKb(MAX_RES)));
	//Test1(new DemodClauseKb(MAX_RES));
	//Test1(new ClauseKb(MAX_RES));
	//Test1(new OtterKb("Test1"));
	//Test1(new JTPKb(JTP_SEARCH_DEPTH));

	//System.out.println("\n\n--------------------\nTest #2\n--------------------");
	//Test2(new CachingKb(new ClauseKb(MAX_RES)));
	//Test2(new DemodClauseKb(MAX_RES));
	//Test2(new ClauseKb(MAX_RES));
	//Test2(new OtterKb("Test2"));
	//Test2(new JTPKb(JTP_SEARCH_DEPTH));
	
	System.out.println("\n\n--------------------\nTest #3\n--------------------");
	//Test3(new CachingKb(new ClauseKb(MAX_RES)));
	//Test3(new DemodClauseKb(MAX_RES));
	//Test3(new ClauseKb(MAX_RES));
	//Test3(new JTPKb(JTP_SEARCH_DEPTH));
	//Test3(new VampireFOFKb(false /*use7*/, 2.0f/*time*/));

	//Test3(new OtterKb(2/*time*/));
	//Test3(new VampireKb(false /*use7*/, 2.0f/*time*/));
	//Test3(new SpassKb(2/*time*/));

	//System.out.println("\n\n--------------------\nTest #4\n--------------------");
	//Test4(new ClauseKb(MAX_RES));
	//Test4(new DemodClauseKb(MAX_RES));
	//Test4(new OtterKb("Test4"));
	//Test4(new JTPKb(JTP_SEARCH_DEPTH));
	
	//System.out.println("\n\n--------------------\nTest #5\n--------------------");
	//Test5(new ClauseKb(MAX_RES));
	//Test5(new DemodClauseKb(MAX_RES));
	//Test5(new OtterKb("Test5"));
	//Test5(new JTPKb(JTP_SEARCH_DEPTH));

	//System.out.println("\n\n--------------------\nTest #6\n--------------------");
	//Test6(new ClauseKb(MAX_RES));
	//Test6(new DemodClauseKb(MAX_RES));
	//Test6(new OtterKb("Test5"));
	//Test6(new JTPKb(JTP_SEARCH_DEPTH));

	CanRefute("~(!E ?b bin(?b,paris,?s)) ^ ~(!E ?b !E ?t tin(?t,paris,?s) ^ on(?b,?t,?s)) ^ ~(!E ?b !E ?c !E ?t tin(?t,?c,?s) ^ on(?b,?t,?s)) ^ (!E ?b !E ?c !E ?t tin(?t,?c,?s) ^ bin(?b,?c,?s))");

	CanRefute("!E ?ba !E ?ta ((!A ?b (~bin(?b,paris,?s) | (!E ?t (tin(?t,paris,?s) ^ ?ba=?b ^ ?ta=?t)))) ^ (!A ?b !A ?t (~tin(?t,paris,?s) | ((!A ?c (~bin(?b,?c,?s) | ~tin(?t,?c,?s) | ?ba~=?b | ?ta~=?t)) ^ ~on(?b,?t,?s)))) ^ (!A ?b !A ?c !A ?t (~tin(?t,?c,?s) | ((!A ?c (~bin(?b,?c,?s) | ~tin(?t,?c,?s) | ?ba~=?b | ?ta~=?t)) ^ ~on(?b,?t,?s)))) ^ (!E ?b !E ?c !E ?t (tin(?t,?c,?s) ^ bin(?b,?c,?s) ^ (!A ?t (~tin(?t,?c,?s) | ?ba~=?b | ?ta~=?t)))))");
    }

    public static void Test1(Kb kb) {

	AddFormulae1(kb);
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("~A" + AMAX + "(c2,c1)") + 
			   "  " + kb.getQueryTime() +
			   " ms, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());

	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("!A ?c1 !A ?c2 ~A" + AMAX + "(?c2,?c1)") + 
			   "  " + kb.getQueryTime() +
			   " ms, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());

	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("A" + AMAX + "(c2,c1)") + 
			   "  " + kb.getQueryTime() +
			   " ms, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());

	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("!E ?c1 !E ?c2 A" + AMAX + "(?c2,?c1)") + 
			   "  " + kb.getQueryTime() +
			   " ms, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());
    }

    public static void AddFormulae1(Kb kb) {
	kb.addFOPCFormula("A1(c1,c2)");
	kb.addFOPCFormula("A1(c3,c4)");
	kb.addFOPCFormula("!A ?x !A ?y A1(?x,?y) => A2(?x,?y)");
	kb.addFOPCFormula("!A ?x !A ?y A1(?x,?y) => A2(?y,?x)");
	for (int i = 1; i < AMAX-1; i++) {
	    kb.addFOPCFormula("!A ?x !A ?y A" + i + "(?x,?y) ^ " + 
			      "A" + (i+1) + "(?x,?y) => A" + (i+2) + "(?x,?y)");
	    kb.addFOPCFormula("!A ?x !A ?y A" + i + "(?x,?y) ^ " + 
			      "A" + (i+1) + "(?x,?y) => A" + (i+2) + "(?y,?x)");
	}
    }

    public static void Test2(Kb kb) {

	String fun = AddFormulae2(kb);
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("A(" + fun.replaceAll("X","c1") + ")") + 
			   "  " + GetElapsedTime() + " ms");
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("~A(" + fun.replaceAll("X","c1") + ")") + 
			   "  " + GetElapsedTime() + " ms");
    }

    public static String AddFormulae2(Kb kb) {

	// Gen seq of length AMAX
	StringBuffer open  = new StringBuffer();
	StringBuffer close = new StringBuffer();
	
	for (int i = 0; i < AMAX; i++) {
	    open.append("f(");
	    close.append(")");
	}

	kb.addFOPCFormula("A(c1)");
	kb.addFOPCFormula("!A ?x A(?x) => A(f(?x))");

	return open.toString() + "X" + close.toString();
    }

    public static void Test3(Kb kb) {

	System.out.println("\n" + kb.getClass() +":\n");

	AddFormulae3(kb);

	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("~NS#LAST(NS#c2,NS#c1)") + 
			   "  " + kb.getQueryTime() +
			   " s, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());

	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("!A ?c1 !A ?c2 ~NS#LAST(?c2,?c1)") + 
			   "  " + kb.getQueryTime() +
			   " s, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());

	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("!E ?c1 !E ?c2 NS#LAST(?c2,?c1)") + 
			   "  " + kb.getQueryTime() +
			   " s, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());
	
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> " + 
			   kb.queryFOPC("NS#LAST(NS#c2,NS#c1)") + 
			   "  " + kb.getQueryTime() +
			   " s, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());
    }

    public static void AddFormulae3(Kb kb) {
       
	kb.addFOPCFormula("NS#FIRST(NS#c1,NS#c2)");
	kb.addFOPCFormula("NS#FIRST(NS#c5,NS#c6)");
	char[] chars = "ABCDE".toCharArray();
	for (int n = 0; n < chars.length; n++) {
	    char c = chars[n];
	    kb.addFOPCFormula("!A ?x !A ?y NS#FIRST(?x,?y) => " + c + "1(?x,?y)");
	    kb.addFOPCFormula("!A ?x !A ?y NS#FIRST(?x,?y) => " + c + "1(?y,?x)");
	    kb.addFOPCFormula("!A ?x !A ?y " + c + (AMAX) + "(?x,?y) => NS#LAST(?x,?y)");
	    kb.addFOPCFormula("!A ?x !A ?y " + c + (AMAX) + "(?x,?y) => NS#LAST(?y,?x)");
	    for (int i = 1; i < AMAX; i++) {
		kb.addFOPCFormula("!A ?x !A ?y " + c + (i) + "(?x,?y) => " + c + (i+1) + "(?x,?y)");
		kb.addFOPCFormula("!A ?x !A ?y " + c + (i) + "(?x,?y) => " + c + (i+1) + "(?y,?x)");
	    }
	}
    }

    public static void CanRefute(String s) {

	Kb kb = new VampireKb(false /*use7*/, 2.0f/*time*/);
	FOPC.Node n = FOPC.parse(s).convertNNF(false);
	FOPC.Node to_refute = n.copy().convertNNF(true);
	System.out.println("Query -> " + n + ": " +
			   kb.queryFOPC(to_refute) + 
			   "\ntime: " + kb.getQueryTime() +
			   " s, cgen: " + kb.getNumInfClauses() + 
			   ", proof-len: " + kb.getProofLength());
    }

    public static void Test4(Kb kb) {

	AddFormulae1(kb);
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPCBindings("A" + AMAX + "(?x,?y)") + 
			   "  " + GetElapsedTime() + " ms");	

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPCBindings("!E ?x A" + AMAX + "(?x,?y)") + 
			   "  " + GetElapsedTime() + " ms");	

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPCBindings("!E ?y A" + AMAX + "(?x,?y)") + 
			   "  " + GetElapsedTime() + " ms");	
    }

    public static void Test5(Kb kb) {

	AddFormulae3(kb);
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPCBindings("LAST(?x,?y)") + 
			   "  " + GetElapsedTime() + " ms");	

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPCBindings("!E ?x LAST(?x,?y)") + 
			   "  " + GetElapsedTime() + " ms");	

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPCBindings("!E ?y LAST(?x,?y)") + 
			   "  " + GetElapsedTime() + " ms");	
    }

    public static void Test6(Kb kb) {

	kb.addFOPCFormula("!A ?x A(?x,?x) => B(?x,?x)");
	kb.addFOPCFormula("A(c,d)");
	kb.addFOPCFormula("c = d");

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPC("B(c,c)") + 
			   "  " + GetElapsedTime() + " ms");	
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPC("B(d,d)") + 
			   "  " + GetElapsedTime() + " ms");	

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPC("B(c,d)") + 
			   "  " + GetElapsedTime() + " ms");	

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPC("B(d,c)") + 
			   "  " + GetElapsedTime() + " ms");	

	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPCBindings("B(?x,?y)") + 
			   "  " + GetElapsedTime() + " ms");	


	ResetTimer();
	System.out.println("Query " + kb.getClass() + " (" + AMAX + ") -> \n" + 
			   kb.queryFOPC("B(e,e)") + 
			   "  " + GetElapsedTime() + " ms");	
    }
}
