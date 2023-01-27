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

public class TestInference4 {

    public static final int MAX_RES = 100;

    public static long _lTime;

    public static void ResetTimer() {
	_lTime = System.currentTimeMillis();
    }

    // Get the elapsed time since resetting the timer
    public static long GetElapsedTime() {
	return System.currentTimeMillis() - _lTime;
    }
    
    public static void main(String args[]) {

	Test1(new VampireKb(5f));
	Test1(new ClauseKb(MAX_RES));
	Test1(new DemodClauseKb(MAX_RES));
    }

    public static void Test1(Kb kb) {

	AddFormulae1(kb);

	// These two false
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " -> " + 
			   kb.queryFOPC("!A ?x below(fa(?x),?x)") + "  " +
			   GetElapsedTime() + " ms");	
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " -> " + 
			   kb.queryFOPC("!A ?x below(fa(fa(?x)),?x)") + "  " +
			   GetElapsedTime() + " ms");	

	// These two true
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " -> " + 
			   kb.queryFOPC("!A ?x above(fa(?x),?x)") + "  " +
			   GetElapsedTime() + " ms");	
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " -> " + 
			   kb.queryFOPC("!A ?x above(fa(fa(?x)),?x)") + "  " +
			   GetElapsedTime() + " ms");	
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " -> " + 
			   kb.queryFOPC("!A ?x above(fa(fa(fa(?x))),?x)") + "  " +
			   GetElapsedTime() + " ms");	
	ResetTimer();
	System.out.println("Query " + kb.getClass() + " -> " + 
			   kb.queryFOPC("!A ?x above(fa(fa(fa(fa(?x)))),?x)") + "  " +
			   GetElapsedTime() + " ms");	
    }

    public static void AddFormulae1(Kb kb) {
	kb.addFOPCFormula("!A ?x !A ?y (!E ?z below(?x,?z) ^ below(?z,?y)) => below(?x,?y)");
	kb.addFOPCFormula("!A ?x !A ?y (!E ?z above(?x,?z) ^ above(?z,?y)) => above(?x,?y)");
	kb.addFOPCFormula("!A ?x !A ?y above(?x,?y) => ?x~=?y");
	kb.addFOPCFormula("!A ?x !A ?y below(?x,?y) => ?x~=?y");
	kb.addFOPCFormula("!A ?x !A ?y above(?x,?y) => ~below(?x,?y)");
	kb.addFOPCFormula("!A ?x !A ?y above(?x,?y) => below(?y,?x)");
	kb.addFOPCFormula("!A ?x !A ?y below(?x,?y) => ~above(?x,?y)");
	kb.addFOPCFormula("!A ?x !A ?y below(?x,?y) => above(?y,?x)");
	kb.addFOPCFormula("!A ?x !A ?y ?x=?y => ~above(?x,?y)");
	kb.addFOPCFormula("!A ?x !A ?y ?x=?y => ~below(?x,?y)");
	kb.addFOPCFormula("!A ?x above(fa(?x),?x)");
	kb.addFOPCFormula("!A ?x below(fb(?x),?x)");
	kb.addFOPCFormula("!A ?x ?x=fa(fb(?x))");
	kb.addFOPCFormula("!A ?x ?x=fb(fa(?x))");
    }
}
