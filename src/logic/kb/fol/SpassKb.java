//////////////////////////////////////////////////////////////////////
//
// First-Order Logic Package
//
// Class:  VampireKb (dumps kb to an otter input file for theorem proving)
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   7/25/03
//
// NOTES:
// ------
//
// **Use fodt.foalp.Case to verify (it first verifies the theorem prover!)**
// **Assumes path to executable binary or script is in working directory**
//
// ---> See logic.kb.cyc for a working example of Vampire 
//      (with scripts and I/O)
//
// TODO:
// -----
// - Should write a simple routine to parse output for query bindings.
//
//////////////////////////////////////////////////////////////////////

package logic.kb.fol;

import java.io.*;
import java.util.*;

import graph.*;
import logic.kb.*;
import logic.kb.fol.parser.*;

public class SpassKb
    extends Kb {

    public static final boolean CONVERT_CNF = true;

    // Commands for DOS and UNIX
    // **Use CMD versions must be used when redirecting IO**
    public final static String DOS_EXE     = "C:\\cygwin\\usr\\bin\\spass";
    public final static String DOS_CMD_EXE = "CMD /C C:\\cygwin\\usr\\bin\\spass";

    public final static String UNIX_EXE     = "spass";
    public final static String UNIX_CMD_EXE = "/bin/sh spass";
 
    public static long   _lTime;

    public String _sKbName;
    public int    _nQuery;
    public Set    _sClauses;
    public int    _nSeconds;
    public int    _nClausesGen;
    public float  _fQueryTime;
    public int    _nClauseCount;
    public int    _nProofLen;
    public FOPC.Node _fopcAssume;
    public String _queryFile;

    private SpassKb() { System.out.println("Must pass SPASS args"); System.exit(1); }

    public SpassKb(int time_out) {
	_sKbName  = "Spass";
	_nQuery   = 1;
	_sClauses = new HashSet();
	_nSeconds = time_out;
	_nProofLen = 0;
	_queryFile = QUERY_FILE;
    }

    public void setQueryFile(String f) {
	_queryFile = f;
    }

    // TODO: Would be nice if could access streams directly and avoid file I/O
    public boolean queryFOPC(String s) {
	return queryFOPC(FOPC.parse(s));
    }

    public boolean queryFOPC(FOPC.Node n) {
	_fopcAssume = null;
	return queryFOPC(n, true);
    }

    public boolean queryFOPC(String assume, String query) {
	return queryFOPC(FOPC.parse(assume), FOPC.parse(query));
    }

    public boolean queryFOPC(FOPC.Node assume, FOPC.Node query) {
	_fopcAssume = assume;
	return queryFOPC(query, true);
    }

    // A bit of a hack, assumes that kb is empty, need to update this code
    // to handle refutation separately from querying, ugly for now.
    public boolean canRefute(FOPC.Node n) {
	_fopcAssume = null;
	return queryFOPC(n, false);
    }

    public boolean canRefute(FOPC.Node assume, FOPC.Node n) {
	_fopcAssume = assume;
	return queryFOPC(n, false);
    }
   
    // A bit of a hack, assumes that kb is empty, need to update this code
    // to handle refutation separately from querying, ugly for now.
    // if prove_query_true is true, checks if query implied (negates and refutes)
    // if prove_query_true is false, checks if refutable
    public boolean queryFOPC(FOPC.Node n, boolean prove_query_true) {
	
	// Generate CNF for negation of query
	n = n.copy();
	if (!genSpassFileForQuery(n, _queryFile, prove_query_true)) {
	    // CNF formulae contained a single FALSE which is a refutation
	    _nClausesGen = -2;
	    _fQueryTime = 0f;
	    return true; // Refutation found
	} else if (_nClauseCount == 0) {
	    return false; // No refutation possible
	}

    	try {
    	       		
	    int index;
	    boolean ref_found = false;
	    _nProofLen = 0;
	    
	    // Open files for reading and writing
	    //BufferedReader fis_reader = new BufferedReader(_rReader);
	    
	    Process p = Runtime.getRuntime().exec(UNIX_EXE + " " + _queryFile + " " + _nSeconds);
	    BufferedReader process_out = new BufferedReader(new InputStreamReader(p.getInputStream()));
	    PrintWriter    process_in  = new PrintWriter(p.getOutputStream(), true);
	    
	    // Provide input to process (could come from any stream)
	    String line = null;
	    //while ((line = fis_reader.readLine()) != null) {
	    //	    process_in.println(line);
	    //}
	    //fis_reader.close();
	    process_in.close(); // Need to close input stream so process exits!!!
	    
	    // Get output from process (can also be used by BufferedReader to get
	    // line-by-line... see how fis_reader is constructed).
	    while ((line = process_out.readLine()) != null) {
		// process line
		//System.out.println("SPASS: " + line);
		if (line.indexOf("Proof found.") >= 0) {
		    ref_found = true;
		} else if ((index = line.indexOf("on the problem")) >= 0) {
		    _fQueryTime = getPrevNum(line, index);
		} else if ((index = line.indexOf("SPASS derived")) >= 0) {
		    _nClausesGen = (int)getNextNum(line, index);
		} else if ((line.indexOf("Here is a proof with depth") >= 0) &&
			   (index = line.indexOf("length")) >= 0) {
		    _nProofLen = (int)getNextNum(line, index);
		} else if (_nProofLen > 0 && 
			   (line.indexOf(":Inp") >= 0 /*|| line.indexOf(":UnC") >= 0*/)) {
		    _nProofLen--;
		}
	    }
	    process_out.close();
	    
	    //System.out.print("Waiting for Spass [" + _fQueryTime + "s, " + _nClausesGen + " clause]...");
	    p.waitFor();
	    //System.out.println("done.");
	    
	    return ref_found;
    		
    	} catch (InterruptedException ie) {
    		System.out.println(ie);
    		return false;
    	} catch (IOException ioe) {
    		System.out.println(ioe);
    		return false;
    	}
    }

    public float getQueryTime() {
	return (float)_fQueryTime;
    }

    public int getNumInfClauses() {
	return _nClausesGen;
    }

    public int getProofLength() {
	return _nProofLen;
    }

    public float getNextNum(String s, int index) {
	StringBuffer num = new StringBuffer();
	while (!Character.isDigit(s.charAt(index))) { index++; }
	while (index < s.length() && (Character.isDigit(s.charAt(index)) || s.charAt(index) == '.')) 
	    { num.append(s.charAt(index++)); }
	try {
	    Float f = new Float(num.toString());
	    return f.floatValue();
	} catch (NumberFormatException e) {
	    return -1;
	}
    }

    public float getPrevNum(String s, int index) {
	StringBuffer num = new StringBuffer();
	while (!Character.isDigit(s.charAt(index))) { index--; }
	while (index > 0 && (Character.isDigit(s.charAt(index)) || s.charAt(index) == '.')) 
	    { num.insert(0, s.charAt(index--)); }
	try {
	    Float f = new Float(num.toString());
	    return f.floatValue();
	} catch (NumberFormatException e) {
	    return -1;
	}
    }

    // Query for bindings of free vars
    public BindingSet queryFOPCBindings(String query) {
	System.out.println("WARNING: Bindings query not implemented for SpassKb yet.");
	return null;
    }

    public BindingSet queryFOPCBindings(String assume, String query) {
	System.out.println("WARNING: Bindings query not implemented for SpassKb yet.");
	return null;
    }

    public BindingSet queryFOPCBindings(FOPC.Node n) {
	System.out.println("WARNING: Bindings query not implemented for SpassKb yet.");
	return null;
    }

    public BindingSet queryFOPCBindings(FOPC.Node assume, FOPC.Node n) {
	System.out.println("WARNING: Bindings query not implemented for SpassKb yet.");
	return null;
    }

    // Generate an otter file for proving this query
    public boolean genSpassFileForQuery(String s) {
	return genSpassFileForQuery(s, _sKbName + "_q" + _nQuery);
    }

    // Generate an otter file for proving this query
    public boolean genSpassFileForQuery(String s, String filename) {
	return genSpassFileForQuery(FOPC.parse(s), filename, true);
    }

    public boolean genSpassFileForQuery(FOPC.Node n, String filename, 
				     boolean prove_query_true) {
	// Generate CNF for negation of query
	Set query = new HashSet();
	FOPC.Node temp_query = n.copy().convertNNF(prove_query_true);
	if (CONVERT_CNF) {
	    System.out.print("c");
	    query.addAll(getClauses(temp_query));
	    System.out.print("[" + (query.size() + _sClauses.size()) + "]");
	} else {
	    System.out.print("f");
	    query.add(temp_query);
	}

	// Dump file
	try {
	    PrintStream os = new PrintStream(new FileOutputStream(filename));

	    // Some file information to verify correctness
	    os.println("% KB " + _sKbName + ", Query #" + _nQuery + 
		       ": FOL Kb generated from logic.kb.fol.SpassKb");
	    //if (!_sClauses.isEmpty()) {
	    //	os.println("% Kb clauses:");
	    //	Iterator ki = _sClauses.iterator();
	    //	while (ki.hasNext()) {
	    //	    os.println("% - " + ((FOPC.Node)ki.next()).toFOLString());
	    //	}
	    //} else {
	    //	os.println("% Empty kb");
	    //}	    
	    os.println("% Testing kb refutation of: " + temp_query.toFOLString());
	    //os.println("% Refuting: " + n.convertNNF(prove_query_true).toFOLString());
	    //if (!query_cnf.isEmpty()) {
	    //	os.println("% Negated query clauses:");
	    //	Iterator qi = query_cnf.iterator();
	    //	while (qi.hasNext()) {
	    //	    os.println("% - " + ((FOPC.Node)qi.next()).toFOLString());
	    //	}
	    //} else {
	    //	os.println("% Empty query");
	    //}
	    _nQuery++; // Increment query for next time
	    os.println();

	    // Print all kb clauses
	    _nClauseCount = 0;
	    int clause_cnt = 1;
	    Set axiom_clauses = new HashSet(_sClauses); // Handle assumptions!
	    if (_fopcAssume != null) {
		axiom_clauses.addAll(getClauses(_fopcAssume));
	    } 
	    Iterator i = axiom_clauses.iterator();

	    while (i.hasNext()) {
		_nClauseCount++;
		FOPC.Node c = (FOPC.Node)i.next();
		
		if (c instanceof FOPC.TNode) {
		    FOPC.TNode tn = (FOPC.TNode)c;
		    if (tn._bValue) {
			continue;
		    } else {
			return false;
		    }
		} 

		os.println("input_clause(clause_" + clause_cnt++ + ",axiom,\n   " + c.toVampireString() + ").\n");
	    }

	    // Print query clause
	    i = query.iterator();
	    while (i.hasNext()) {
		_nClauseCount++;
		FOPC.Node c = (FOPC.Node)i.next();
		
		if (c instanceof FOPC.TNode) {
		    FOPC.TNode tn = (FOPC.TNode)c;
		    if (tn._bValue) {
			continue;
		    } else {
			return false;
		    }
		} 

		os.println("input_clause(clause_" + clause_cnt++ + ",conjecture,\n   " + c.toVampireString() + ").\n");
	    }
	    os.close();
	    //System.out.println("Generated " + _nClauseCount + " clauses.");

	} catch (IOException ioe) {
	    System.out.println("Error: " + ioe);
	    System.exit(1);
	}

	return true;
    }

    // Convert a first-order formula to clauses and add to kb
    public void addFOPCFormula(String s) {
	_sClauses.addAll(getClauses(FOPC.parse(s)));
    }

    public void addFOPCFormula(FOPC.Node n) {
	_sClauses.addAll(getClauses(n));
    }

    // Remove duplicate clauses
    public Set filterClauses(Set clauses) {
	HashSet ret = new HashSet();
	HashSet tmp = new HashSet();
	Iterator i = clauses.iterator();
	while (i.hasNext()) {
	    FOPC.ConnNode c = (FOPC.ConnNode)i.next();
	    tmp.clear();
	    tmp.addAll(c._alSubNodes); // Removes duplicates!
	    FOPC.ConnNode r = new FOPC.ConnNode(c._nType);
	    Iterator j = tmp.iterator();
	    boolean tautology    = false;
	    boolean inconsistent = false;
	    while (!tautology && !inconsistent && j.hasNext()) {
		FOPC.Node nn = (FOPC.Node)j.next();

		if (nn instanceof FOPC.TNode) {
		    FOPC.TNode tn = (FOPC.TNode)nn;
		    if (tn._bValue) {
			tautology = true;
			break;
		    } else {
			if (tmp.size() == 1) {
			    inconsistent = true;
			}
			continue;
		    }
		} 

		r.addSubNode(nn);
	    }

	    if (!tautology) {
		if (inconsistent) {
		    ret.add(new FOPC.TNode(false));
		} else {
		    ret.add(r);
		}
	    }
	}
	return ret;
    }

    public Set getClauses(FOPC.Node n) {

	// DNF conversion to push down quantifiers is pointless here
	// since we'll get rid of EXISTS and CNF(DNF) will yield
	// an exponential blowup with simplification.
	boolean SAVED_ALLOW_DNF = FOPC.ALLOW_DNF;
	FOPC.ALLOW_DNF = false;
	HashSet ret = new HashSet();

	// Simpify n and convert to NNF
	n = n.copy(); // Following functions may modify original!
	n = FOPC.simplify(n); 
	n = FOPC.skolemize(n);
	n = FOPC.convertCNF(n);

	//System.out.println("Generating clauses for: " + n.toFOLString());

	// Break apart top-level, standardize apart free vars, and add to clause list
	if ((n instanceof FOPC.ConnNode) && 
	    ((FOPC.ConnNode)n)._nType == FOPC.ConnNode.AND) {

	    // Go through all subclauses
	    Iterator i = ((FOPC.ConnNode)n)._alSubNodes.iterator();
	    while (i.hasNext()) {
		FOPC.Node sn = (FOPC.Node)i.next();

		// Reality check!
		if (! (((sn instanceof FOPC.ConnNode) && 
			((FOPC.ConnNode)sn)._nType == FOPC.ConnNode.OR)
		       || (sn instanceof FOPC.PNode)
		       || (sn instanceof FOPC.TNode))) {

		    System.out.println("CNF conversion was bad: " + sn.toFOLString());
		    System.exit(1);
		}
	
		if (sn instanceof FOPC.PNode) {
		    FOPC.ConnNode cn = new FOPC.ConnNode(FOPC.ConnNode.OR);
		    cn.addSubNode(sn);
		    ret.add(cn);
		} else {
		    ret.add(sn);
		}
	    }

	} else {
	    if (! (((n instanceof FOPC.ConnNode) && 
		    ((FOPC.ConnNode)n)._nType == FOPC.ConnNode.OR)
		   || (n instanceof FOPC.PNode)
		   || (n instanceof FOPC.TNode))) {
		
		System.out.println("CNF conversion was bad: " + n.toFOLString());
		System.exit(1);
	    }
	    
	    if (n instanceof FOPC.PNode || n instanceof FOPC.TNode) {
		FOPC.ConnNode cn = new FOPC.ConnNode(FOPC.ConnNode.OR);
		cn.addSubNode(n);
		ret.add(cn);
	    } else {
		ret.add(n); 
	    } 
	}

	// Restore DNF conversion
	FOPC.ALLOW_DNF = SAVED_ALLOW_DNF;
	return filterClauses(ret); // Remove duplicates!!!
    }


    public static void ResetTimer() {
	_lTime = System.currentTimeMillis();
    }

    // Get the elapsed time since resetting the timer
    public static long GetElapsedTime() {
	return System.currentTimeMillis() - _lTime;
    }
}
