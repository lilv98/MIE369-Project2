//////////////////////////////////////////////////////////////////////
//
// First-Order Logic Package (Theorem Proving Examples)
//
// Class:  MultipleQueries 
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Description: This file shows that Send all the queries all at once, then 
// Query 3 is not proved. But, if only Query 3 and Query 4 are sent, then 
// Query 3 is proved. We believe that this suggest that (1) it is better to send
// one query each time, (2) "not proved" might mean that resource is run out 
// to give a proof, but nothing more than this. 
//
//////////////////////////////////////////////////////////////////////

package logic.kb.fol;

import java.io.*;
import java.text.*;
import java.util.*;
import logic.kb.*;

public class TestInference2 {

    public static DecimalFormat _df = new DecimalFormat("0.##");

    public static void main(String args[]) {
    //String userdir = System.getProperty("user.dir"); System.out.println("dir..."+userdir);
	//System.out.println("\nUsing Otter theorem prover:");
	//System.out.println("---------------------------");
	//DoExample(new OtterKb("Examples" /* Just a kb name of your choice */));

	System.out.println("Using Vampire theorem prover:");
	System.out.println("-----------------------------");
	
	DoExample(new VampireKb(false, 5.0f /* Time limit of 5 seconds */));

	// These are Java-based theorem provers, they are not very efficient
	// and I doubt anyone would find them useful unless they need to
	// retrieve parameter bindings.
	// DoExample(new ClauseKb(MAX_RES));
	// DoExample(new DemodClauseKb(MAX_RES));
	// DoExample(new CachingKb(new ClauseKb(MAX_RES))); // Caches results for reuse
    }

    public static void DoExample(Kb kb) {
        

	// pslcore.	

	kb.addFOPCFormula("!A ?t1 !A ?t2  ( before(?t1, ?t2) => timepoint(?t1) ^ timepoint(?t2) )");
	kb.addFOPCFormula("!A ?t1 !A ?t2  ( timepoint(?t1) ^ timepoint(?t2) =>   ?t1 = ?t2 | before(?t1, ?t2) | before(?t2, ?t1) )");
	kb.addFOPCFormula("!A ?t1  ( ~ before(?t1, ?t1) )");
	kb.addFOPCFormula("!A ?t1 !A ?t2 !A ?t3  ( before(?t1, ?t2) ^ before(?t2, ?t3) => before(?t1, ?t3) )");
	kb.addFOPCFormula("!A ?t  ( timepoint(?t) ^ ~ (?t = minusInf) => before(minusInf, ?t) )");
	kb.addFOPCFormula("!A ?t  ( timepoint(?t) ^ ~ (?t = plusInf) => before(?t, plusInf) )");
	kb.addFOPCFormula("!A ?End  ( timepoint(?End) ^ ~ (?End = minusInf) =>    !E ?u ( between(minusInf, ?u, ?End) ) )");
	kb.addFOPCFormula("!A ?Beg  ( timepoint(?Beg) ^ ~ (?Beg = plusInf) =>    !E ?u ( between(?Beg, ?u, plusInf) ) )");
	kb.addFOPCFormula("!A ?x  ( activity(?x) | activity_occurrence(?x) | timepoint(?x) | object(?x) )");
	kb.addFOPCFormula("!A ?x  ( ( activity(?x) =>  ~ ( activity_occurrence(?x) | object(?x) | timepoint(?x) ) ) ^ ( activity_occurrence(?x) =>  ~ ( object(?x)  | timepoint(?x) ) )  ^  ( object(?x) =>  ~ timepoint(?x) ) )");  
	kb.addFOPCFormula("!A ?a !A ?occ  ( occurrence_of(?occ, ?a) =>  ( activity(?a) ^ activity_occurrence(?occ) ) )");
	kb.addFOPCFormula("!A ?occ  ( activity_occurrence(?occ) => !E ?a ( activity(?a) ^ occurrence_of(?occ, ?a) ) )");
	kb.addFOPCFormula("!A ?occ !A ?a1 !A ?a2  ( occurrence_of(?occ, ?a1) ^ occurrence_of(?occ, ?a2) =>  ?a1 = ?a2 )");
	kb.addFOPCFormula("!A ?a !A ?x  ( ( occurrence_of(?x, ?a) | object(?x) ) =>    ( timepoint(beginof(?x)) ^ timepoint(endof(?x)) ) )");
	kb.addFOPCFormula("!A ?a !A ?x  ( activity_occurrence(?x) | object(?x) =>    beforeEq(beginof(?x), endof(?x)) )");
	kb.addFOPCFormula("!A ?x !A ?occ !A ?t  ( participates_in(?x, ?occ, ?t) =>    object(?x) ^ activity_occurrence(?occ)^ timepoint(?t) )");
	kb.addFOPCFormula("!A ?x !A ?occ !A ?t  ( participates_in(?x, ?a, ?t) =>    exists_at(?x, ?t) ^ is_occurring_at(?occ, ?t) )");
	kb.addFOPCFormula("!A ?t1 !A ?t2 !A ?t  ( between(?t1, ?t2, ?t3) <=>    before( ?t1, ?t2) ^ before(?t2, ?t3) )");
	kb.addFOPCFormula("!A ?t1 !A ?t2  ( beforeEq(?t1, ?t2) <=>  ( timepoint(?t1) ^ (timepoint(?t2) ^ ( before(?t1, ?t2) | ?t1 = ?t2 )) ))");
	kb.addFOPCFormula("!A ?t1 !A ?t2 !A ?t3  ( betweenEq(?t1, ?t2, ?t3) <=> beforeEq(?t1, ?t2) ^ beforeEq(?t2, ?t3))");
	kb.addFOPCFormula("!A ?x !A ?t  ( exists_at(?x, ?t) <=>    object(?x) ^ betweenEq(beginof(?x), ?t, endof(?x)) )");
	kb.addFOPCFormula("!A ?occ !A ?t ( is_occurring_at(?occ, ?t) <=> activity_occurrence(?occ) ^ betweenEq(beginof(?occ), ?t,endof(?occ)) )");

	// atomic. 

	kb.addFOPCFormula("!A  ?a  ( primitive(?a) => atomic(?a) )");
	kb.addFOPCFormula("!A  ?a  ( ?a = conc(?a, ?a) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2  ( conc(?a1, ?a2) = conc(?a2, ?a1) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2 !A ?a3  ( conc(?a1, conc(?a2, ?a3)) = conc(conc(?a1, ?a2), ?a3) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2  ( atomic(conc(?a1, ?a2)) <=>    ( atomic(?a1) ^ atomic(?a2) ) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2  ( ( atomic(?a1) ^ atomic(?a2) ) =>    ( subactivity(?a1, ?a2) <=>  ?a2 = conc(?a1, ?a2) ) )");

	//kb.addFOPCFormula("!A  ?a1 !A ?a2  ( atomic(?a2) =>    ( subactivity(?a1, ?a2) <=>  !E ?a3  ( ?a2 = conc(?a1, ?a3) ) ) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2  ( atomic(?a2) =>    ( subactivity(?a1, ?a2) <=>  !E ?a3  ( atomic(?a3) ^ ?a2 = conc(?a1, ?a3) ) ) )");

	//kb.addFOPCFormula("!A  ?a !A ?b0 !A ?b1  ( ( subactivity(?a, conc(?b0, ?b1)) ^ ~ primitive(?a) ) =>  !E ?a0 !E ?a1 ( subactivity(?a0, ?a) ^  subactivity(?a1, ?a) ^  ?a = conc(?a0, ?a1) ) )");
	kb.addFOPCFormula("!A  ?a !A ?b0 !A ?b1  ( ( atomic(?a) ^ atomic(?b0) ^ atomic(?b1) ^ subactivity(?a, conc(?b0, ?b1)) ^ ~ primitive(?a) ) =>  !E ?a0 !E ?a1 ( subactivity(?a0, ?a) ^  subactivity(?a1, ?a) ^  ?a = conc(?a0, ?a1) ) )");

	kb.addFOPCFormula("!A  ?s !A ?a  ( ( occurrence(?s, ?a) ^ legal(?s) ) => atomic(?a) )"); //12/June/2006
	//kb.addFOPCFormula("!A ?a  ( atomic(?a) <=> ( !E ?s initial(?s) ^ occurrence_of(?s, ?a)) ) ");

	//  new
	kb.addFOPCFormula("!A  ?a  ( atomic(?a) => activity(?a) )");

	// state.
	kb.addFOPCFormula("!A ?f  ( state(?f) => object(?f) )");
	kb.addFOPCFormula("!A ?f !A ?occ  holds(?f, ?occ) =>  ( state(?f) ^ activity_occurrence(?occ) )");
	kb.addFOPCFormula("!A ?f !A ?occ  ( prior(?f, ?occ) => ( state(?f) ^ activity_occurrence(?occ) ) )");
	kb.addFOPCFormula("!A ?occ1 !A ?occ2  !A ?f  ( ( initial(?occ1) ^ initial(?occ2) ) =>    ( prior(?f, ?occ1) <=> prior(?f, ?occ2) ) )");
	kb.addFOPCFormula("!A ?a  !A ?occ  ( holds(?f ,?occ) <=>    prior(?f, successor(?a ,?occ)) )");

	//kb.addFOPCFormula("!A ?occ1 !A ?f  (   holds(?f, ?occ1) => !E ?occ2  ( precedes(?occ2, ?occ1) ^   holds(?f, ?occ2) ^ ( initial(?occ2) | ~ prior(?f, ?occ2)) ^ !A ?occ3  ( ( precedes(?occ2, ?occ3) ^ precedes(?occ3, ?occ1) ) =>  holds(?f, ?occ3) ) ) )");
	kb.addFOPCFormula("!A ?occ1 !A ?f  (   holds(?f, ?occ1) => !E ?occ2  ( earlierEq(?occ2, ?occ1) ^   holds(?f, ?occ2) ^ ( initial(?occ2) | ~ prior(?f, ?occ2)) ^ !A ?occ3  ( ( earlier(?occ2, ?occ3) ^ earlier(?occ3, ?occ1) ) =>  holds(?f, ?occ3) ) ) )");                

	//kb.addFOPCFormula("!A ?occ1 !A ?f  ( ~ holds(?f, ?occ1) => !E ?occ2  ( earlierEq(?occ2, ?occ1) ^ ~ holds(?f, ?occ2) ^ ( initial(?occ2) |   prior(?f, ?occ2)) ^  ~ !E ?occ3  ( earlier(?occ2, ?occ3) ^ earlier(?occ3, ?occ1) ^  holds(?f, ?occ3) ) ) )");    
	//kb.addFOPCFormula("!A ?occ1 !A ?f  ( ~ holds(?f, ?occ1) => !E ?occ2  ( precedes(?occ2, ?occ1) ^ ~ holds(?f, ?occ2) ^ ( initial(?occ2) |   prior(?f, ?occ2)) ^  ~ !E ?occ3  ( precedes(?occ2, ?occ3) ^ precedes(?occ3, ?occ1) ^  holds(?f, ?occ3) ) ) )");    
	kb.addFOPCFormula("   (!A ?occ1 !A ?f ( ((~ holds(?f, ?occ1)) ^  state(?f) ^ activity_occurrence(?occ1)) =>   (!E ?occ2 earlierEq(?occ2, ?occ1) ^  (~ holds(?f, ?occ2))  ^ ( initial(?occ2) | prior(?f, ?occ2))   ^ (~ (!E ?occ3  (activity_occurrence(?occ3) ^ earlier(?occ2, ?occ3) ^ earlier(?occ3, ?occ1) ^   holds(?f, ?occ3)) ))  )))");

	// occtree.
	kb.addFOPCFormula("!A ?s1 !A ?s2  ( earlier(?s1, ?s2) =>    activity_occurrence(?s1) ^ activity_occurrence(?s2) )");
	kb.addFOPCFormula("!A ?s1 !A ?s2  ( earlier(?s1, ?s2) =>    ~ earlier(?s2, ?s1) )");
	kb.addFOPCFormula("!A ?s1 !A ?s2 !A ?s3  ( earlier(?s1, ?s2) ^ earlier(?s2, ?s3) =>  earlier(?s1, ?s3) )");
	kb.addFOPCFormula("!A ?s1 !A ?s2 !A ?s3  ( earlier(?s1, ?s2) ^ earlier(?s3, ?s2) => earlier(?s1, ?s3) | earlier(?s3, ?s1) | ?s3 = ?s1 )");

	//kb.addFOPCFormula("!A ?s1  ( initial(?s1) <=> ~ !E ?s2 ( earlier(?s2,?s1) ) )");
	kb.addFOPCFormula("!A ?s1  ( initial(?s1)  <=> activity_occurrence(?s1) ^ ~ (!E ?s2  earlier(?s2,?s1) ) )");

	kb.addFOPCFormula("!A ?s1 !A ?s2  ( earlier(?s1, ?s2) =>  !E ?sp  ( initial(?sp) ^ (earlierEq(?sp, ?s1) | ?sp = ?s1) ) )");

	kb.addFOPCFormula("!A ?a  ( activity(?a) =>    !E ?s  ( occurrence_of(?s, ?a) ^ initial(?s) ) )"); // June/12/2006
	//kb.addFOPCFormula("!A ?s1 !A ?s2 !A ?a  ( ( earlier(?s1, ?s2) ^ occurrence_of(?s2, ?a) )=>  !E ?s  ( occurrence_of(?s, ?a) ^ initial(?s) ) )");

	kb.addFOPCFormula("!A ?s1 !A ?s2 !A ?a  ( initial(?s1) ^ initial(?s2) ^   occurrence_of(?s1, ?a) ^ occurrence_of(?s2, ?a) =>  ?s1 = ?s2 )");

	kb.addFOPCFormula("!A ?a !A ?s  ( activity(?a) ^ activity_occurrence(?s) =>    occurrence_of(successor(?a, ?s), ?a) )"); //June/12/2006
	//kb.addFOPCFormula("!A ?a !A ?s  ( (activity_occurrence(?s)^ (!E ?s1 (initial(?s1) ^ occurrence_of(?s1, ?a)) )) <=> occurrence_of(successor(?a, ?s), ?a) )");

	//kb.addFOPCFormula("!A ?s  ( ~ initial(?s) =>    !E ?a  !E ?sp  ( ?s = successor(?a, ?sp) ) )");
	kb.addFOPCFormula("!A ?s  ( ~ initial(?s) ^ activity_occurrence(?s)=>    !E ?a  !E ?sp  ( ?s = successor(?a, ?sp) ) )");

	kb.addFOPCFormula("!A ?a !A ?s1 !A ?s2  ( earlier(?s1, successor(?a, ?s2)) <=> earlierEq(?s1, ?s2) )");

	kb.addFOPCFormula("!A ?s  ( legal(?s) => activity_occurrence(?s) )"); //12/June/2006
	//kb.addFOPCFormula("!A ?s  ( legal(?s) => (initial(?s) | (!E ?sp earlier(?sp, ?s))) )");


	kb.addFOPCFormula("!A ?s1 !A ?s2  ( legal(?s1) ^ earlier(?s2, ?s1) => legal(?s2) )");
	kb.addFOPCFormula("!A ?s1 !A ?s2  ( earlier(?s1, ?s2) =>  before(endof(?s1), beginof(?s2)) )");
	kb.addFOPCFormula("(!A ?s1 !A ?s2  ( precedes(?s1, ?s2) <=> (earlier(?s1, ?s2) ^ legal(?s2)) ))");

	//kb.addFOPCFormula("!A ?s1 !A ?s2  ( earlierEq(?s1, ?s2) <=>    earlier(?s1, ?s2) | ?s1 = ?s2 )");
	//kb.addFOPCFormula("!A ?occ1 !A ?occ2 (earlierEq(?occ1, ?occ2) => (activity_occurrence(?occ1) ^ activity_occurrence(?occ2)) )");
	//kb.addFOPCFormula("!A ?s1  !A ?s2 (earlierEq(?s1, ?s2) <=> (earlier(?s1, ?s2) | ( activity_occurrence(?s1) ^   activity_occurrence(?s2) ^  (?s1=?s2))))");
	kb.addFOPCFormula("!A ?s1  !A ?s2 (earlierEq(?s1, ?s2) <=>  ( activity_occurrence(?s1) ^   activity_occurrence(?s2) ^  (earlier(?s1, ?s2) |?s1=?s2)))");

	kb.addFOPCFormula("!A ?a  !A ?s  ( poss(?a, ?s) <=> legal(successor(?a, ?s)) )");

	// subactivity.

	kb.addFOPCFormula("!A  ?a1 !A ?a2  ( subactivity(?a1 ,?a2) =>    ( activity(?a1) ^ activity(?a2) ) )");
	kb.addFOPCFormula("!A  ?a  ( activity(?a) =>    subactivity(?a, ?a) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2  ( ( subactivity(?a1, ?a2) ^  subactivity(?a2, ?a1) ) => ?a1 = ?a2 )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2 !A ?a3  ( ( subactivity(?a1, ?a2) ^      subactivity(?a2, ?a3) ) =>  subactivity(?a1, ?a3) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2 ( subactivity(?a1, ?a2) => !E ?a3 ( subactivity(?a1, ?a3) ^ subactivity(?a3, ?a2) ^  !A ?a4 ( ( subactivity(?a1, ?a4) ^ subactivity(?a4, ?a3) ) => ( ?a4 = ?a1 | ?a4 = ?a3 ) ) ) )");
	kb.addFOPCFormula("!A  ?a1 !A ?a2 ( subactivity(?a1, ?a2) => !E ?a3 ( subactivity(?a1, ?a3) ^ subactivity(?a3, ?a2) ^  !A ?a4 ( ( subactivity(?a3, ?a4) ^ subactivity(?a4, ?a2) ) => ( ?a4 = ?a2 | ?a4 = ?a3 ) ) ) )"); 

	//kb.addFOPCFormula("!A  ?a !A ?a1  ( primitive(?a) <=>    ( subactivity(?a1, ?a) => ?a1 = ?a ))");
	//kb.addFOPCFormula("!A  ?a !A ?a1  ( primitive(?a) <=>  (activity(?a) ^  ( subactivity(?a1, ?a) => (?a1 = ?a) )))");
	kb.addFOPCFormula("!A  ?a  ( primitive(?a) <=>  (activity(?a) ^ (!A ?a1 ( subactivity(?a1, ?a) => (?a1 = ?a)))   ))");

	kb.addFOPCFormula("primitive(fry)");
	kb.addFOPCFormula("primitive(boil)");
	kb.addFOPCFormula("primitive(wash)");

	kb.addFOPCFormula("!A ?o initial(?o) => ~ prior(water, ?o)");
	kb.addFOPCFormula("!A ?o initial(?o) =>  prior(clean, ?o)");

	// precondition axioms.

	kb.addFOPCFormula("!A ?o occurrence_of(?o, fry) ^ legal(?o) => prior(clean,?o)");
	kb.addFOPCFormula("!A ?o occurrence_of(?o, boil) ^ legal(?o) => prior(clean,?o)");
	kb.addFOPCFormula("!A ?o occurrence_of(?o, wash) ^ legal(?o) => prior(water,?o)");

	// successor state axioms.
	kb.addFOPCFormula("!A ?o holds(clean,?o) <=> (prior(clean, ?o) ^ (~ occurrence_of(?o, fry)) ^ activity_occurrence(?o)) | occurrence_of(?o, wash)");
	kb.addFOPCFormula("!A ?o holds(water,?o) <=> prior(water, ?o)");


	kb.addFOPCFormula("fry ~= boil");
	kb.addFOPCFormula("fry ~= wash");
	kb.addFOPCFormula("boil ~= wash");

	kb.addFOPCFormula("!A ?a primitive(?a) <=> (?a = boil | ?a = fry | ?a = wash)");


	kb.addFOPCFormula("!A ?s occurrence_of(?s, fry) ^ prior(clean,  ?s) ^ initial(?s)  => legal(?s) ");
	kb.addFOPCFormula("!A ?s occurrence_of(?s, boil) ^ prior(clean, ?s) ^ initial(?s)  => legal(?s)");
	kb.addFOPCFormula("!A ?s occurrence_of(?s, wash) ^ prior(water, ?s) ^ initial(?s)  => legal(?s)");
	kb.addFOPCFormula("!A ?s legal(?s) ^ prior(clean, successor(fry,  ?s)) => legal(successor(fry,  ?s))");
	kb.addFOPCFormula("!A ?s legal(?s) ^ prior(clean, successor(boil, ?s)) => legal(successor(boil, ?s))");
	kb.addFOPCFormula("!A ?s legal(?s) ^ prior(water, successor(wash, ?s)) => legal(successor(wash, ?s))");
  
	//query1
	//QueryKb(kb, " !E ?o occurrence_of(?o, fry) ^ legal(?o)");
	//query2
	//QueryKb(kb, " !E ?o occurrence_of(?o, fry) ^ legal(?o)");
        //query3	
 	QueryKb(kb, "!E ?o1 !E ?o2  occurrence_of(?o1, fry) ^ occurrence_of(?o2, boil) ^ precedes(?o2, ?o1) ");

	if (!already) {
	    already = true;
	    //query4
	    QueryKb(kb, "!E ?o1 !E ?o2  occurrence_of(?o1, fry) ^ occurrence_of(?o2, boil) ^ precedes(?o1, ?o2) ");
	    //query5
	    QueryKb(kb, "!E ?o1 !E ?o2  occurrence_of(?o1, fry) ^ occurrence_of(?o2, boil) ^ earlier(?o1, ?o2)"); 
	    //query6
	    QueryKb(kb, "!E ?o1 !E ?o2  occurrence_of(?o1, fry) ^ occurrence_of(?o2, boil) ^ earlier(?o2, ?o1)"); 
	}
    }

    public static boolean already = true;

    public static void QueryKb(Kb kb, String query) {
	System.out.print("Query:  " + query + " --> ");
	System.out.println(" Result: " + (kb.queryFOPC(query) ? "*PROVED*." : "*NOT PROVED*."));
	System.out.println("Stats:  " + _df.format(kb.getQueryTime()) + " seconds, " + 
			   kb.getNumInfClauses() + " clauses generated, " +  
			   kb.getProofLength() + " proof length.");
	System.out.println();
    }
}
