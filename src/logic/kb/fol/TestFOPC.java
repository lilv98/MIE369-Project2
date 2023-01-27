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

public class TestFOPC {
    
    public static void main(String args[]) {
	FOPC.Node n = FOPC.parse("(!A ?t !E ?c tin(?t,?c,?s)) ^ ((!E ?t !E ?b on(?b,?t,?s)) ^ (!A ?b ~bin(?b,paris,?s)) ^ (!A ?t ((!A ?b ~on(?b,?t,?s)) | ~tin(?t,paris,?s))) ^ (!A ?t ((!A ?c ~tin(?t,?c,?s)) | (!A ?b ~on(?b,?t,?s)))) ^ (!E ?c ((!E ?t tin(?t,?c,?s)) ^ (!E ?b bin(?b,?c,?s)))))");
	/*FOPC.Node n = FOPC.parse("(!E ?ta !E ?ba (!E ?t ((((!E ?b ((!E ?c (bin(?b,?c,?s) ^ tin(?t,?c,?s))) ^ ?ba=?b)) ^ ?ta=?t) | (!E ?b on(?b,?t,?s))) ^ tin(?t,paris,?s)))) ^ " + 
				 "(!A ?b ~bin(?b,paris,?s)) ^ " + 
				 "(!A ?t ((!A ?b ~on(?b,?t,?s)) | ~tin(?t,paris,?s))) ^ " + 
				 "(!A ?t ((!A ?c ~tin(?t,?c,?s)) | (!A ?b ~on(?b,?t,?s)))) ^ " + 
				 "(!E ?c ((!E ?t tin(?t,?c,?s)) ^ (!E ?b bin(?b,?c,?s)))) ^ " + 
				 "(!A ?t !A ?c1 !A ?c2 (tin(?t,?c1,?s) ^ tin(?t,?c2,?s)) => ?c1=?c2)");
	*/	

	FOPC.Node s = FOPC.simplify(n);

	System.out.println("Original: " + n);
	System.out.println("\n\nSimplify: " + s);
    }
}
