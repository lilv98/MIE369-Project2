//////////////////////////////////////////////////////////////////////
//
// First-Order Logic Package
//
// Class:  GroundKb (recursively evaluates predicates under closed-world
//                   assumption and possibly a domain closure assumption)
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   1/20/05
//
// NOTES:
// ------
// - It seems to me that most efficiency will have to derive from
//   pushing quantifiers down as far as possible (currently done in 
//   FOPC.java pushDownQuant()) and from typing.
// - Can also propagate conjuncts to prune in some cases.
//
// TODO:
// -----
// - For now, assuming all predicates are ground.  See PrologKb for
//   a Horn rule, SLD-resolution version of this KB.
// - 
//
//////////////////////////////////////////////////////////////////////

package logic.kb.fol;

import java.io.*;
import java.util.*;

import graph.*;
import logic.kb.*;
import util.*;

/**
 * GroundKb class
 * 
 */
public class GroundKb extends Kb {

    public final static boolean USE_CACHE = false;
	
    public GroundDomain _gDomain;
    public HashMap _hmBindingsCache;  // Maps a standardized query node to binding set
    public HashMap _hmGroundPred;
    public HashMap _hmTPID2Bindings;  // Cache for non-fluent transitive bindings
    public String  _sQueryFile;
    public int     _nTopType = -1;
	
    public interface GroundDomain {
		
	public int  addPredicate(FOPC.PNode pred);
	public int  addType(FOPC.PNode type);
	public int  setPredSlotType(FOPC.PNode pred, int slot, FOPC.PNode type);
	public int  addTypeInstance(FOPC.PNode type, FOPC.Term inst);
	public boolean addPredBinding(FOPC.PNode pred, ArrayList instances);

	// Use to mark specifically as fluent or non-fluent
	public void markAsFluent(String pred, int arity, boolean is_fluent);
	public boolean isFluentPID(int pid);
	public boolean isNonFluentPID(int pid);

	public void clearGroundAssertions();
	public void clearGroundAssertions(String pred, int arity);
	public void clearGroundFluents();

	public int        getPredID(FOPC.PNode pred);
	public int        getInstanceID(FOPC.Term inst);
	public FOPC.PNode getPredName(int id);
	public FOPC.PNode getTypeName(int id);
	public int        getPredSlotType(int pred_id, int slot);
	public FOPC.Term  getInstanceName(int id);
	public IntSet     getTypeInstances(int type);
	public HashSet    getPredBindings(int pred);

	public ArrayList getTerms(IntArray terms);
	public ArrayList getTerms(IntSet terms);
	public String printTerms(IntArray terms);
	public String printTerms(IntSet terms);
	
	// Return -1 if illegal
	public int getTypeJoin(int tid_1, int tid_2);
		
	// Future (for DL): Return null if not composable
	// public FOPC.PNode conjoinTypes(FOPC.PNode p1, FOPC.PNode p2);
    }

    // CWA assumed, domain closure optional (specify as false if domain is null)
    public GroundKb(GroundDomain dgen) {
	_gDomain = dgen;
	_hmBindingsCache = new HashMap();
	_hmGroundPred    = new HashMap();
	_hmTPID2Bindings = new HashMap();
    }

    public float getQueryTime() {
	System.out.println("TODO: GroundKb.getQueryTime");
	return -1f;
    }

    public int getNumInfClauses() {
	System.out.println("TODO: GroundKb.getNumInfClauses");
	return -1;
    }

    public int getProofLength() {
	System.out.println("TODO: GroundKb.getProofLen");
	return -1;
    }

    public void setQueryFile(String s) {
	_sQueryFile = s;
    }
	
    public boolean queryFOPC(String s) {
	return queryFOPC(FOPC.parse(s));
    }

    public void clearGroundAssertions() {
	_gDomain.clearGroundAssertions();
    }

    public void clearGroundAssertions(String pred, int arity) {
	_gDomain.clearGroundAssertions(pred, arity);
    }

    public void markAsFluent(String pred, int arity, boolean is_fluent) {
	_gDomain.markAsFluent(pred, arity, is_fluent);
    }

    public void clearGroundFluents() {
	_gDomain.clearGroundFluents();
    }

    public void clearCache() {
	_hmBindingsCache.clear();
    }
	
    // Returns true if support found.
    public boolean queryFOPC(FOPC.Node n) {
	n = n.copy().convertNNF(false);
	Bindings start = new Bindings(new ArrayList(), new ArrayList());
	start._bindings.add(new IntArray());
	Bindings b = eval(n, start, false);
	return b._bindings.size() > 0;
    }

    public boolean queryFOPC(String assume, String query) {
	return queryFOPC(FOPC.parse(assume), FOPC.parse(query));
    }

    public boolean queryFOPC(FOPC.Node assume, FOPC.Node query) {
	FOPC.ConnNode imp = new FOPC.ConnNode(FOPC.ConnNode.IMPLY, assume, query);
	return queryFOPC(imp);
    }

    // See below
    public BindingSet queryFOPCBindings(String query) {
	return queryFOPCBindings(FOPC.parse(query));
    }

    // Query for bindings of free vars
    public BindingSet queryFOPCBindings(FOPC.Node n) {
		
	// Convert n to NNF (and copy)
	n = n.copy().convertNNF(false);
	Bindings start = new Bindings(new ArrayList(), new ArrayList());
	start._bindings.add(new IntArray());
	Bindings b = eval(n, start, false);
	//System.out.println("Before convert: " + b);
	return b.convert2BindingSet();
    }

    public BindingSet queryFOPCBindings(String assume, String query) {
	return queryFOPCBindings(FOPC.parse(assume), FOPC.parse(query));
    }

    public BindingSet queryFOPCBindings(FOPC.Node assume, FOPC.Node query) {
	FOPC.ConnNode imp = new FOPC.ConnNode(FOPC.ConnNode.IMPLY, assume, query);
	return queryFOPCBindings(imp);
    }

    // Instances are Strings as well
    public void addType(String type, ArrayList instances) {
		
	FOPC.PNode ptype = new FOPC.PNode(false, type);   
	ptype._nArity = 1;
	_gDomain.addType(ptype);		
	Iterator i = instances.iterator();
	while (i.hasNext()) {
	    FOPC.TFunction inst = new FOPC.TFunction((String)i.next());
	    _gDomain.addTypeInstance(ptype, inst);
	}
    }

    // Top type to be used for ambiguous joons
    public void setTopType(String type) {
	FOPC.PNode ptype = new FOPC.PNode(false, type);   
	ptype._nArity = 1;
	_nTopType = _gDomain.addType(ptype);
    }
	
    public void addPredicate(String name, ArrayList types) {

	FOPC.PNode ppred = new FOPC.PNode(false, name);
	ppred._nArity = types.size();
	_gDomain.addPredicate(ppred);
	    
	for (int i = 0; i < types.size(); i++) {
	    String type = (String)types.get(i);
	    FOPC.PNode ptype = new FOPC.PNode(false, type);   
	    ptype._nArity = 1;
	    _gDomain.setPredSlotType(ppred, i, ptype);
	}
    }
	
    ////////////////////////////////////////////////////////////////////////////
	
    // See below
    public void addFOPCFormula(String s) {
	addFOPCFormula(FOPC.parse(s));
    }
	
    // Must be a ground atom or a FOPC.ConnNode, handled accordingly
    public void addFOPCFormula(FOPC.Node n) {

	if (n instanceof FOPC.PNode) {
	    addGroundBinding((FOPC.PNode) n);
	} else {
	    System.out.println("GroundKb: Can only assert implications");
	    System.exit(1);
	}
    }

    // Add a ground binding - *** deletes binding if negated!
    public void addGroundBinding(String s) {
	addGroundBinding((FOPC.PNode)FOPC.parse(s));
    }
	
    // Add a ground binding - *** deletes binding if negated!
    public void addGroundBinding(FOPC.PNode p) {

	// Verify all bindings are constants or constant functions
	ArrayList terms = p._alTermBinding;
	Iterator i = terms.iterator();
	while (i.hasNext()) {
	    FOPC.Term t = (FOPC.Term) i.next();
	    Set vars = t.collectVars();
	    if (!vars.isEmpty()) {
		System.out.println("Cannot assert nonground PNode.");
		System.out.println("PNode: " + p.toFOLString());
		return;
	    }
	}

	// OK, so add bindings
	_gDomain.addPredBinding(p, p._alTermBinding);
    }
	
    public int[] _nv_index = new int[20];
    public int[] _tids    = new int[20];
    public boolean[] _include = new boolean[20];
	
    public Bindings getGroundBindings(FOPC.PNode p) {

	// First check for a transitive pnode
	boolean transitive = false;
	if (p._sPredName.endsWith("@") && p._nArity == 2) {
	    transitive = true;
	    FOPC.PNode temp_p = (FOPC.PNode)p.copy();
	    temp_p._sPredName = p._sPredName.substring(0,p._sPredName.length()-1);
	    p = temp_p;
	}

	int pid = _gDomain.getPredID(p);
	if (pid == -1) {
	    System.out.println("No ground bindings for: " + p);
	    return null;
	}
	Bindings b = new Bindings(p._alTermBinding, new ArrayList());
	HashSet bindings = _gDomain.getPredBindings(pid);
		
	// Complete the bindings if transitive
	// TODO: May want to cache this in the future
	if (transitive) {

	    HashSet trans_cache = null;
	    if (_gDomain.isNonFluentPID(pid) && 
		(trans_cache = (HashSet)_hmTPID2Bindings.get(new Integer(pid))) != null) {

		// If pid is specifically marked a non-fluent and we have cached
		// results then we can reuse them
		//System.out.println("Using cache: " + p + "\n" + trans_cache);
		bindings = trans_cache;

	    } else {

		// Two ways to do this... either with depth-first search (used here)
		// or via repeated joins/projections (probably more efficient for
		// large sets?).
		
		// Get a set of all first-index vars
		bindings = (HashSet)bindings.clone();
		IntSet first_index = new IntSet();
		Iterator i = bindings.iterator();
		while (i.hasNext()) {
		    IntArray ia = (IntArray)i.next();
		    first_index.add(ia.l[0]);
		}
		
		// For each first index, get a set of its transitive closure
		TreeSet rel = new TreeSet(bindings);
		for (int j = 0; j < first_index.count; j++) {
		    int first = first_index.l[j];
		    IntSet trans_closure = transClosure(rel, first);
		    
		    // Now insert each relation into bindings
		    for (int k = 0; k < trans_closure.count; k++) {
			IntArray entry = new IntArray();
			entry.add(first);
			entry.add(trans_closure.l[k]);
			bindings.add(entry);
		    }
		}

		_hmTPID2Bindings.put(new Integer(pid), bindings);
	    }
	}

	// Now go through bindings, noting the vars and non-vars
	int non_vars = 0;
	_nv_index = new int[b._vars.size()];
	_tids     = new int[b._vars.size()];
	ArrayList new_vars = new ArrayList();
	ArrayList types    = new ArrayList();
	for (int i = 0; i < b._vars.size(); i++) {
	    FOPC.Term t = (FOPC.Term)b._vars.get(i);
	    if (t instanceof FOPC.TVar) {
		new_vars.add(t);
		types.add(new Integer(_gDomain.getPredSlotType(pid, i)));
		_include[i] = true;
	    } else {
		_nv_index[non_vars] = i;
		_tids[non_vars++] = _gDomain.getInstanceID(t);
		_include[i] = false;
	    }
	}
		
	// Filter constants out of bindings
	Iterator it = bindings.iterator();
	HashSet new_bindings = new HashSet();
	while (it.hasNext()) {
	    IntArray ia = (IntArray)it.next();
	    boolean match = true;
	    for (int i = 0; match && i < non_vars; i++) {
		match = (ia.l[_nv_index[i]] == _tids[i]);
	    }
	    //System.out.println(ia + ": match: " + match);
	    if (!match) continue;
	    IntArray na = new IntArray();
	    for (int i = 0; i < ia.count; i++) {
		if (_include[i]) {
		    na.add(ia.l[i]);
		}
	    }
	    new_bindings.add(na);
	}
		
	b._vars = new_vars;
	b._types = types;
	b._bindings = new_bindings;
		
	return b;
    }
	
    // --------------- BEGIN Transitive Closure Helper ----------------

    IntSet _isTrans = new IntSet();
    
    // Node could be problems if this return value is modified,
    // or used after the method is called a second time.
    public IntSet transClosure(TreeSet rel, int key) {
	IntSet ret = new IntSet();
	IntArray a = getAllMatches(rel, key);
	for (int i = 0; i < a.count; i++) {
	    ret.addAll(reflTransClosure(rel, a.l[i]));
	}
	return ret;
    }

    public IntSet reflTransClosure(TreeSet rel, int key) {
	_isTrans.clear();
	reflTransClosureInt(rel, key);
	return _isTrans;
    }
    
    public void reflTransClosureInt(TreeSet rel, int key) {
	if (_isTrans.contains(key)) {
	    return;
	}
	_isTrans.add(key);
	IntArray a = getAllMatches(rel, key);
	for (int i = 0; i < a.count; i++) {
	    reflTransClosureInt(rel, a.l[i]);
	}
    }

    public IntArray getAllMatches(TreeSet table, int first_num) {
	IntArray ret = new IntArray();

	IntArray ia_min = new IntArray(); 
	ia_min.add(first_num); 
	ia_min.add(0);

	IntArray ia_max = new IntArray();
	ia_max.add(first_num); 
	ia_max.add(Integer.MAX_VALUE - 1);
	
	// Interesting problem here with overflow if use MIN_VALUE
	SortedSet subset = table.subSet(ia_min, ia_max);
	Iterator i = subset.iterator();
	while (i.hasNext()) {
	    IntArray ia_next = (IntArray)i.next();
	    ret.add(ia_next.l[1]);
	}

	return ret;
    }

    // --------------- END Transitive Closure Helper ----------------

    // ///////////////////////////////////////////////////////////////////////////////////////

    public Bindings eval(FOPC.Node n, Bindings so_far, boolean negate) {

	Bindings ret = null;
	if (!USE_CACHE || ((ret = (Bindings) _hmBindingsCache.get(n.toFOLString())) == null)) {

	    // n = n.pushDownQuant();
	    n.setFreeVars();
	    if (n instanceof FOPC.QNode) {

		ret = evalQuant((FOPC.QNode) n, so_far, negate, 0 /* index */);

	    } else if (n instanceof FOPC.ConnNode) {

		ret = evalConn((FOPC.ConnNode) n, so_far, negate);

	    } else if (n instanceof FOPC.PNode) {

		FOPC.PNode p = (FOPC.PNode) n;
		if (p._nPredID == FOPC.PNode.EQUALS) {
		    // System.out.println("EVAL EQUALITY");
		    ret = evalEquality(p, so_far, negate);
		} else {
		    ret = evalGround(p, so_far, negate);
		}

	    } else if (n instanceof FOPC.NNode) {

		ret = eval(((FOPC.NNode) n)._subnode, so_far, !negate);

	    } else if (n instanceof FOPC.TNode) {

		boolean bval = ((FOPC.TNode)n)._bValue;
		if (negate) bval = !bval;

		if (bval) {
		    return so_far;
		} else {
		    // Return empty bindings
		    return new Bindings((ArrayList)so_far._vars.clone(), 
					(ArrayList)so_far._types.clone());
		}

	    } else { // Error: unhandled node

		System.out.println("Error: " + n.toFOLString()
				   + " not handled by current interpreter");
		System.exit(1);
	    }

	    if (ret != null) {
		if (USE_CACHE) {
		    _hmBindingsCache.put(n.toFOLString(), ret);
		}
				// System.out.println("- Return size: " + ret._bindings.size());
	    }
	}

	return ret;
    }

    public Bindings evalQuant(FOPC.QNode q, Bindings so_far, 
			      boolean negate, int index) {

	// Base case
	if (index == q._alQuantType.size()) {
	    return eval(q._subnode, so_far, negate);
	}

	// Recursive case
	int quant = ((Integer)q._alQuantType.get(index)).intValue();
	FOPC.TVar var = (FOPC.TVar)q._alQuantBinding.get(index);

	if ((quant == q.EXISTS && !negate) ||
	    (quant == q.FORALL && negate)) {
	    
	    Bindings b = evalQuant(q, so_far, negate, index + 1);
	    return Project(b, var);

	} else {

	    // Need to double negate here (always evaluate neg on its own)
	    Bindings single = new Bindings(new ArrayList(), new ArrayList());
	    single._bindings.add(new IntArray());
	    Bindings b = evalQuant(q, single, !negate /* First negate */, index + 1);
	    Bindings neg = Project(b, var);
	    
	    // First negation handled during recursion
	    return Join(so_far, neg, true /* Second negate */); 
	}
    }

    public Bindings evalConn(FOPC.ConnNode c, Bindings so_far, boolean negate) {

	if ((c._nType == FOPC.ConnNode.AND && !negate) ||
	    (c._nType == FOPC.ConnNode.OR  && negate)) {

	    // Handle conjunction
	    Bindings ret = so_far;
	    Iterator i = c._alSubNodes.iterator();
	    // System.out.println("CONJ: " + c.toFOLString());
	    while (i.hasNext() && ret._bindings.size() > 0) { // Exit early if bindings empty
		FOPC.Node n = (FOPC.Node) i.next();
		
		// Semantics for eval is to conjoin sub-query with so_far 
		ret = eval(n, ret, negate);
	    }
	    // System.out.println("Final:\n" + ret);
	    return ret;

	} else if ((c._nType == FOPC.ConnNode.OR  && !negate) ||
		   (c._nType == FOPC.ConnNode.AND && negate)) {

	    // Need to double negate here (always evaluate neg on its own)
	    Bindings single = new Bindings(new ArrayList(), new ArrayList());
	    single._bindings.add(new IntArray());

	    // Handle conjunction
	    Bindings neg = single;
	    Iterator i = c._alSubNodes.iterator();
	    // System.out.println("CONJ: " + c.toFOLString());
	    while (i.hasNext() && neg._bindings.size() > 0) { // Exit early if bindings empty
		FOPC.Node n = (FOPC.Node) i.next();
		
		// Semantics for eval is to conjoin sub-query with so_far 
		neg = eval(n, neg, !negate);
	    }
	    // System.out.println(
	    
	    // First negation handled during recursion
	    return Join(so_far, neg, true /* Second negate */); 
	    
	} else if (c._nType == FOPC.ConnNode.IMPLY) {
	    return evalConn(new FOPC.ConnNode(FOPC.ConnNode.OR, new FOPC.NNode(
					      (FOPC.Node) c._alSubNodes.get(0)),
					      (FOPC.Node) c._alSubNodes.get(1)), so_far, negate);
	} else {

	    // Invalid!!!
	    System.out.println("Invalid connective ID: " + c._nType);
	    System.out.println(c.toFOLString());
	    System.exit(1);
	    return null;
	}
    }

    // Conjunctive semantics, could be negated!
    // 
    public Bindings evalEquality(FOPC.PNode p, Bindings so_far, boolean negate) {

	// Check for (in)equality
	if (p._bIsNegated) negate = !negate;

	//System.out.println(p._sPredName + ", " + p._nPredID);
	if (p._nPredID == FOPC.PNode.EQUALS) {

	    FOPC.Term lhs = (FOPC.Term) p._alTermBinding.get(0);
	    FOPC.Term rhs = (FOPC.Term) p._alTermBinding.get(1);
	    boolean lhs_is_var = lhs instanceof FOPC.TVar;
	    boolean rhs_is_var = rhs instanceof FOPC.TVar;

	    if ((!lhs_is_var && !rhs_is_var) || lhs.equals(rhs)) {

		// No vars
		if ((!negate && lhs.equals(rhs)) ||
		    ( negate && !lhs.equals(rhs))) {
		    // Return so_far ^ true
		    return so_far;
		} else {
		    // Return so_far ^ false = false
		    return new Bindings((ArrayList)so_far._vars.clone(), 
					(ArrayList)so_far._types.clone());
		}

	    } else if (lhs_is_var && rhs_is_var) {
		
		// Both are vars - make sure both in so_far
		int lhs_index = so_far._vars.indexOf(lhs);
		int rhs_index = so_far._vars.indexOf(rhs);
		if (lhs_index < 0 || rhs_index < 0) {
		    System.out.println("ERROR: = vars: " + lhs + ", " + rhs + 
				       " must both be bound: " + so_far._vars + ": " + p);
		    return null;
		}

		// Now go through so_far, retaining rows that satisfy (in)equality
		Bindings ret = new Bindings(so_far._vars, so_far._types);
		Iterator i = so_far._bindings.iterator();
		while (i.hasNext()) {
		    IntArray ia = (IntArray)i.next();
		    if (!negate && (ia.l[lhs_index] == ia.l[rhs_index]) ||
			negate  && (ia.l[lhs_index] != ia.l[rhs_index])) {
			ret._bindings.add(ia);
		    }
		}
		return ret;

	    } else {
		
		// One is a var - make sure it is LHS
		if (rhs_is_var) {
		    FOPC.Term tmp = lhs;
		    lhs = rhs;
		    rhs = tmp;
		}
		
		int lhs_index  = so_far._vars.indexOf(lhs);
		int inst_id = _gDomain.getInstanceID(rhs);
		if (lhs_index < 0 || inst_id < 0) {
		    System.out.println("ERROR: = var: " + lhs + " must be bound: " + 
				       so_far._vars);
		    return null;
		}

		// Now go through so_far, retaining rows that satisfy (in)equality
		Bindings ret = new Bindings(so_far._vars, so_far._types);
		Iterator i = so_far._bindings.iterator();
		while (i.hasNext()) {
		    IntArray ia = (IntArray)i.next();
		    if (!negate && (ia.l[lhs_index] == inst_id) ||
			negate  && (ia.l[lhs_index] != inst_id)) {
			ret._bindings.add(ia);
		    }
		}
		return ret;
	    }
	} 

	System.out.println("EvalEquality ERROR: " + p.toFOLString());
	return null;
    }

    //public HashSet _pIn   = new HashSet();
    //public HashSet _pPred = new HashSet();
	
    // We're assuming a Join (conjunctive) semantics with so_far
    public Bindings evalGround(FOPC.PNode p, Bindings so_far, boolean negate) {

	if (p._bIsNegated) negate = !negate;
		
	Bindings gb = getGroundBindings(p);
	//System.out.println("gb return: " + gb);
	Bindings ret = null;
		
	//_pIn.clear();   _pIn.addAll(so_far._vars);
	//_pPred.clear(); _pPred.addAll(gb._vars);

	ret = Join(so_far, gb, negate);
		
	//System.out.println("Returning:\n" + ret);
	return ret;
    }

    // ///////////////////////////////////////////////////////////////////////////////////////

    // For index i on LHS, what is corresponding index for RHS?
    public int[] b1_to_ret = new int[20];
    public int[] b2_to_ret = new int[20];
    public int[] b2_to_b1  = new int[20];

    // If negate_b2 then negates b2
    public Bindings Join(Bindings b1, Bindings b2, boolean negate_b2) {

	//System.out.println("Joining:");
	//System.out.println(b1);
	//System.out.println(b2);

	// If negate_b2 and b2 vars not a subset of b1 then need to
	// formally negate.
	if (negate_b2) {
	    if (SuperSet(new HashSet(b1._vars), new HashSet(b2._vars))) {
		return JoinNeg(b1, b2);
	    } else {
		b2 = Negate(b2);
	    }
	}
	    
	// Generate superset of vars
	HashSet tvars = new HashSet(b1._vars);
	tvars.addAll(b2._vars);
	ArrayList new_vars = new ArrayList(tvars);
	ArrayList types = new ArrayList();
	Iterator it = new_vars.iterator();
	while (it.hasNext()) {
	    FOPC.TVar t = (FOPC.TVar)it.next();
	    int index1 = b1._vars.indexOf(t);
	    int index2 = b2._vars.indexOf(t);
	    if (index1 >= 0 && index2 >= 0) {
		int tid1 = ((Integer)b1._types.get(index1)).intValue();
		int tid2 = ((Integer)b2._types.get(index2)).intValue();
		int joinType = _gDomain.getTypeJoin(tid1, tid2);
		if (joinType == -1) {
		    if (_nTopType == -1) {
			System.out.println("ILLEGAL JOIN: USING DEFAULT OF " + _nTopType);
			System.out.println(b1._vars + ", " + b1._types);
			System.out.println(b2._vars + ", " + b2._types);
			System.exit(1);
		    }
		    types.add(new Integer(_nTopType));
		} else {
		    types.add(new Integer(joinType));
		}
	    } else if (index1 >= 0) {
		types.add(b1._types.get(index1));
	    } else if (index2 >= 0) {
		types.add(b2._types.get(index2));
	    } else {
		System.out.println("ERROR: VAR " + t + " NOT IN EITHER BINDING!");
		System.out.println(b1._vars + ", " + b1._types);
		System.out.println(b2._vars + ", " + b2._types);
		return null;
	    }
	}
	Bindings ret = new Bindings(new_vars, types);
	IntArray entry = new IntArray();
	int i;

	// Generate map from b1 to ret, and b2 to ret
	for (i = 0; i < b1._vars.size(); i++) {
	    FOPC.TVar v = (FOPC.TVar) b1._vars.get(i);
	    b1_to_ret[i] = new_vars.indexOf(v);
	}
	for (i = 0; i < b2._vars.size(); i++) {
	    FOPC.TVar v = (FOPC.TVar) b2._vars.get(i);
	    b2_to_b1[i]  = b1._vars.indexOf(v); // -1 if not found
	    b2_to_ret[i] = new_vars.indexOf(v);
	}

	// Go through each element in b1 and b2...
	// For each b1 subset that matches b2, add
	// the entry to ret

	// System.out.println("B1: " + b1._bindings.size() + ", " + b1._vars);
	Iterator j = b1._bindings.iterator();
	while (j.hasNext()) {
	    IntArray bind1 = (IntArray) j.next();
	    entry.clear();
	    for (i = 0; i < b1._vars.size(); i++) {
		entry.set(b1_to_ret[i], bind1.l[i]);
	    }
	    // System.out.println("B2: " + b2._bindings.size() + ", " +
	    // b2._vars);
	    Iterator k = b2._bindings.iterator();
	    while (k.hasNext()) {
		IntArray bind2 = (IntArray) k.next();
		boolean match = true;
		for (i = 0; i < b2._vars.size(); i++) {
		    if (b2_to_b1[i] >= 0) { // Exists a match
			if (bind1.l[b2_to_b1[i]] != bind2.l[i]) {
			    match = false;
			    break; // Not a match, skip bind2
			} // Otherwise a match
		    } else { // Not in b1, so add it to entry
			entry.set(b2_to_ret[i], bind2.l[i]);
		    }
		}
		if (match) {
		    // If we got here, must be a match
		    ret._bindings.add(entry.clone());
		} 
	    }
	}
	
	return ret;
    }
    
    // In this case, b2 is known to be a subset of b1 so we are
    // just removing entries from b2
    public Bindings JoinNeg(Bindings b1, Bindings b2) {
	
	Bindings ret = (Bindings)b1.clone();
	int i;

	for (i = 0; i < b2._vars.size(); i++) {
	    FOPC.TVar v = (FOPC.TVar) b2._vars.get(i);
	    b2_to_b1[i]  = b1._vars.indexOf(v); // -1 if not found
	}

	// Go through each element in b1 and b2...
	// For each b1 subset that matches b2, add
	// the entry to ret

	// System.out.println("B1: " + b1._bindings.size() + ", " + b1._vars);
	Iterator j = b1._bindings.iterator();
	while (j.hasNext()) {
	    IntArray bind1 = (IntArray) j.next();

	    Iterator k = b2._bindings.iterator();
	    while (k.hasNext()) {
		IntArray bind2 = (IntArray) k.next();
		boolean match = true;
		for (i = 0; i < b2._vars.size(); i++) {
		    if (b2_to_b1[i] >= 0) { // Exists a match
			if (bind1.l[b2_to_b1[i]] != bind2.l[i]) {
			    match = false;
			    break; // Not a match, skip bind2
			} // Otherwise a match
		    } else { // Not in b1, so add it to entry
			System.out.println("CANNOT USE JOINNEG: "  + b1._vars + "/" + b2._vars);
			return null;
		    }
		}
		if (match) {
		    // If we got here, must be a match
		    ret._bindings.remove(bind1);
		} 
	    }
	}

	return ret;
    }

    public Bindings Project(Bindings b, FOPC.TVar to_remove) {

	// Get new set of vars
	int var_index = b._vars.indexOf(to_remove);
	if (var_index < 0) {

	    // We obviously terminated a CONJ before we reached this var
	    // but since there were no bindings, we can just return the
	    // empty binding set
	    if (b._bindings.size() == 0) {
		return b;
	    }

	    System.out.println("GroundKb Project ERROR: "
			       + to_remove.toFOLString());
	    System.out.println(b);
	    // Will cause ArrayIndex Exception
	}
	ArrayList new_vars  = (ArrayList) b._vars.clone();
	ArrayList new_types = (ArrayList) b._types.clone();
	new_vars.remove(var_index);
	new_types.remove(var_index);
	Bindings ret = new Bindings(new_vars, new_types);

	// Now copy and remove var_index in each binding
	Iterator i = b._bindings.iterator();
	while (i.hasNext()) {
	    IntArray newb = (IntArray)((IntArray)i.next()).clone();
	    newb.removeIndex(var_index);
	    ret._bindings.add(newb);
	}

	return ret;
    }

    // If neg false then *unions* otherwise *subtracts*
    public Bindings Union(Bindings b1, Bindings b2, boolean negate_b2) {

	//System.out.println("Union:");
	//System.out.println(b1);
	//System.out.println(b2);

	if (!(new HashSet(b1._vars)).equals(new HashSet(b2._vars))) {
	    System.out.println("Cannot union non-equivalent var sets");
	    System.out.println("B1: " + b1._vars);
	    System.out.println("B2: " + b2._vars);
	}

	// Check if vars align... then just combine directly
	if (b1._vars.equals(b2._vars)) {
	    Bindings ret = new Bindings(b1._vars, b1._types);
	    ret._bindings.addAll(b1._bindings);
	    ret._bindings.addAll(b2._bindings);
	    return ret;
	}

	int sz = b1._vars.size();
	Bindings ret = new Bindings(b1._vars, b1._types);
	ret._bindings.addAll(b1._bindings);

	int[] b1_to_b2 = new int[sz];
	int index;
	for (index = 0; index < sz; index++) {
	    b1_to_b2[index] = b2._vars.indexOf(b1._vars.get(index));
	}

	Iterator i = b2._bindings.iterator();
	while (i.hasNext()) {
	    IntArray bindings = (IntArray) i.next();
	    IntArray entry = new IntArray();
	    for (index = 0; index < sz; index++) {
		entry.add(bindings.l[b1_to_b2[index]]);
	    }
	    if (negate_b2) {
		ret._bindings.remove(entry);
	    } else {
		ret._bindings.add(entry);
	    }
	}
		
	//System.out.println("Union result:\n" + ret._bindings);
		
	return ret;
    }


    // This can be extremely inefficient because |domain|^|vars|
    // Should try to focus on => constraint method.
    public Bindings Negate(Bindings b) {

	Bindings all = genFullBindings(b._vars, b._types);
	all._bindings.removeAll(b._bindings);

	return all;
    }


    public Bindings genFullBindings(ArrayList vars, ArrayList types) {

	Bindings b = new Bindings(vars, types);
	genRecurse(b, 0, new IntArray());
	return b;
    }
    
    // Returns ArrayList of ArrayLists of all combinations of elements in domain
    public void genRecurse(Bindings b, int i, IntArray ia) {
	if (i == b._vars.size()) {
	    b._bindings.add(ia.clone());
	} else {

	    int tid = ((Integer)b._types.get(i)).intValue();
	    IntSet is = _gDomain.getTypeInstances(tid);
	    for (int j = 0; j < is.count; j++) {
		ia.set(i, is.l[j]);
		genRecurse(b, i+1, ia);
	    }
	}
    }
	
    // ///////////////////////////////////////////////////////////////////////////////////////

    // Helper function for set determination: true if 'a' superset of 'b'
    public static boolean SuperSet(Set a, Set b) {
	Iterator i = b.iterator();
	while (i.hasNext()) {
	    if (!a.contains(i.next())) {
		return false;
	    }
	}
	return true;
    }

    // Dump the kb
    public String toString() {
	StringBuffer sb = new StringBuffer();
	sb.append("****************  Ground Kb  **************\n");
	sb.append(_gDomain.toString());
	sb.append("*******************************************\n");
	return sb.toString();
    }

    // ///////////////////////////////////////////////////////////////////////////////////////

    /**
     * Internal representation of bindings
     */
    public class Bindings {
	public ArrayList _vars; // List of TVars (same width as _bindings
	public ArrayList _types;
	// sublists)

	public HashSet _bindings; // A set of lists (where sublists
	// corresponds to vars)

	// and contains instances of TFunction

	public Bindings(ArrayList vars, ArrayList types) {
	    _vars = vars;
	    _types = types;
	    _bindings = new HashSet();
	}

	public Object clone() {
	    Bindings b = new Bindings((ArrayList) _vars.clone(), 
                                      (ArrayList) _types.clone());
	    b._bindings.addAll(_bindings);
	    return b;
	}

	public ArrayList getVars() {
	    return _vars;
	}

	public int getNumEntries() {
	    return _bindings.size();
	}

	// HashSet automatically checks redundancy
	public void addEntry(IntArray bindings) {
	    _bindings.add(bindings);
	}

	public boolean containsEntry(IntArray bindings) {
	    return _bindings.contains(bindings);
	}

	public Iterator getIterator() {
	    return _bindings.iterator();
	}

	public String toString() {
	    StringBuffer sb = new StringBuffer("Var order: [ ");
	    Iterator i = _vars.iterator();
	    while (i.hasNext()) {
		FOPC.TVar v = (FOPC.TVar) i.next();
		sb.append(v.toFOLString() + " ");
	    }
	    sb.append("]\n");

	    i = _bindings.iterator();
	    int index = 0;
	    while (i.hasNext()) {
		sb.append(index + ": [");
		IntArray ia = (IntArray)i.next();
		sb.append(_gDomain.printTerms(ia));
		sb.append(" ]\n");
		index++;
	    }
	    return sb.toString();
	}

	public BindingSet convert2BindingSet() {

	    BindingSet bs = new BindingSet();
	    Iterator i = _vars.iterator();
	    Iterator ti = _types.iterator();
	    while (i.hasNext()) {
		int tid = ((Integer)ti.next()).intValue();
		String type = _gDomain.getTypeName(tid)._sPredName;
		bs.addVar(((FOPC.TVar) i.next()).toFOLString(), 
			  type);
	    }

	    Iterator j = _bindings.iterator();
	    while (j.hasNext()) {
		IntArray ia = (IntArray) j.next();
		ArrayList binding = _gDomain.getTerms(ia);
		i = _vars.iterator();
		Iterator k = binding.iterator();
		int entry_id = bs.makeNewBindingEntry();
		while (i.hasNext()) {
		    bs.addBinding(entry_id, ((FOPC.TVar) i.next())
				  .toFOLString(), ((FOPC.Term) k.next())
				  .toFOLString());
		}
	    }

	    return bs.seal();
	}
    }

    // Build a simple test kb
    public static void main(String[] args) {
	//Test1();
	Test2();
	//Test3();
    }

    public static void Test1() {
	SimpleDomain sd = new SimpleDomain();
		
	FOPC.PNode box   = new FOPC.PNode(false, "box");   box._nArity = 1;
	FOPC.PNode truck = new FOPC.PNode(false, "truck"); truck._nArity = 1;
	FOPC.PNode city  = new FOPC.PNode(false, "city");  city._nArity = 1;

	FOPC.PNode bin = new FOPC.PNode(false, "bin"); bin._nArity = 2;
	FOPC.PNode tin = new FOPC.PNode(false, "tin"); tin._nArity = 2;
	FOPC.PNode on  = new FOPC.PNode(false, "on");   on._nArity = 2;
		
	FOPC.Term b1 = new FOPC.TFunction("b1");
	FOPC.Term b2 = new FOPC.TFunction("b2");
	FOPC.Term b3 = new FOPC.TFunction("b3");
		
	FOPC.Term t1 = new FOPC.TFunction("t1");
	FOPC.Term t2 = new FOPC.TFunction("t2");
	FOPC.Term t3 = new FOPC.TFunction("t3");
		
	FOPC.Term c1 = new FOPC.TFunction("c1");
	FOPC.Term c2 = new FOPC.TFunction("c2");
	FOPC.Term c3 = new FOPC.TFunction("c3");
		
	sd.addType(box); sd.addType(truck); sd.addType(city);
	sd.addPredicate(bin); sd.addPredicate(tin); sd.addPredicate(on);
	sd.setPredSlotType(bin, 0, box); sd.setPredSlotType(bin, 1, city);
	sd.setPredSlotType(tin, 0, truck); sd.setPredSlotType(tin, 1, city);
	sd.setPredSlotType(on,  0, box); sd.setPredSlotType(on,  1, truck);
		
	sd.addTypeInstance(box, b1); sd.addTypeInstance(box, b2); sd.addTypeInstance(box, b3);
	sd.addTypeInstance(truck, t1); sd.addTypeInstance(truck, t2); sd.addTypeInstance(truck, t3);
	sd.addTypeInstance(city, c1); sd.addTypeInstance(city, c2); sd.addTypeInstance(city, c3);

	ArrayList a1 = new ArrayList(); a1.add(b1); a1.add(c1); sd.addPredBinding(bin, a1);
	a1.clear(); a1.add(b2); a1.add(c2); sd.addPredBinding(bin, a1);
	a1.clear(); a1.add(b3); a1.add(c3); sd.addPredBinding(bin, a1);
		
	a1.clear(); a1.add(t1); a1.add(c2); sd.addPredBinding(tin, a1);
	a1.clear(); a1.add(t2); a1.add(c3); sd.addPredBinding(tin, a1);
	a1.clear(); a1.add(t3); a1.add(c1); sd.addPredBinding(tin, a1);
		
	a1.clear(); a1.add(b1); a1.add(t1); sd.addPredBinding(on, a1);
	a1.clear(); a1.add(b2); a1.add(t1); sd.addPredBinding(on, a1);
		
	System.out.println(sd);
    }

    public static void Test2() {

	SimpleDomain sd = new SimpleDomain();
	GroundKb kb = new GroundKb(sd);

	ArrayList boxes = new ArrayList(); 
	boxes.add("b1"); boxes.add("b2"); boxes.add("b3");
	kb.addType("box", boxes);

	ArrayList trucks = new ArrayList();
	trucks.add("t1"); trucks.add("t2"); trucks.add("t3");
	kb.addType("truck", trucks);

	ArrayList cities = new ArrayList(); 
	cities.add("c1"); cities.add("c2"); cities.add("c3");
	kb.addType("city", cities);

	ArrayList bin_types = new ArrayList();
	bin_types.add("box"); bin_types.add("city");
	kb.addPredicate("bin", bin_types);

	ArrayList tin_types = new ArrayList();
	tin_types.add("truck"); tin_types.add("city");
	kb.addPredicate("tin", tin_types);

	ArrayList on_types = new ArrayList();
	on_types.add("box"); on_types.add("truck");
	kb.addPredicate("on", on_types);

	ArrayList conn_types = new ArrayList();
	conn_types.add("city"); conn_types.add("city");
	kb.addPredicate("conn", conn_types);

	kb.addGroundBinding("on(b1,t1)");
	kb.addGroundBinding("on(b2,t1)");
	kb.addGroundBinding("tin(t1,c2)");
	kb.addGroundBinding("tin(t2,c3)");
	kb.addGroundBinding("tin(t3,c1)");
	kb.addGroundBinding("bin(b3,c3)");
	kb.addGroundBinding("bin(b2,c2)");
	kb.addGroundBinding("bin(b1,c1)");

	kb.addGroundBinding("conn(c1,c2)");
	kb.addGroundBinding("conn(c2,c3)");
	
	PrintQuery(kb, "on(?b,?t)");
	PrintQuery(kb, "tin(?t,?c)");
	PrintQuery(kb, "bin(?b,?c)");
		
	PrintQuery(kb, "on(?b,t1)");
	PrintQuery(kb, "tin(t1,?c)");
	PrintQuery(kb, "tin(?t,c1)");
	PrintQuery(kb, "tin(t1,c2)");
	PrintQuery(kb, "tin(t2,c2)");
		
	PrintQuery(kb, "tin(?t,?c1) ^ bin(?b,?c2)");
	PrintQuery(kb, "tin(?t,?c1) ^ bin(?b,?c2) ^ ~tin(?t,?c2)"); 
	PrintQuery(kb, "!E ?t tin(?t,?c1) ^ bin(?b,?c2) ^ ~tin(?t,?c2)"); 
	PrintQuery(kb, "!E ?t !E ?c1 tin(?t,?c1) ^ bin(?b,?c2) ^ ~tin(?t,?c2)"); 
	PrintQuery(kb, "!E ?t !E ?c1 !E ?b tin(?t,?c1) ^ bin(?b,?c2) ^ ~tin(?t,?c2)"); 
	PrintQuery(kb, "!E ?t !E ?c1 !E ?b !E ?c2 tin(?t,?c1) ^ bin(?b,?c2) ^ ~tin(?t,?c2)"); 
	PrintQuery(kb, "!A ?c2 !E ?t !E ?c1 !E ?b tin(?t,?c1) ^ bin(?b,?c2) ^ ~tin(?t,?c2)"); 
	PrintQuery(kb, "!A ?c2 !A ?t !E ?c1 !E ?b tin(?t,?c1) ^ bin(?b,?c2) ^ ~tin(?t,?c2)"); 
	PrintQuery(kb, "!A ?t !A ?c tin(?t,?c) => tin(?t,?c)");
	PrintQuery(kb, "!A ?t !A ?c ~tin(?t,?c) => tin(?t,?c)");
	PrintQuery(kb, "~tin(?t,?c)");
	PrintQuery(kb, "~bin(?b,?c)");
	PrintQuery(kb, "~tin(?t,?c) | ~bin(?b,?c)");
	PrintQuery(kb, "tin(?t,?c) ^ bin(?b,?c)");
	PrintQuery(kb, "tin(t1,?c) ^ bin(?b,?c)");
	PrintQuery(kb, "(~tin(?t,?c) | ~bin(?b,?c)) ^ c1 = c1");
	PrintQuery(kb, "(~tin(?t,?c) | ~bin(?b,?c)) ^ c2 = c1");
	PrintQuery(kb, "(~tin(?t,?c) | ~bin(?b,?c)) ^ c2 ~= c1");
	PrintQuery(kb, "(~tin(?t,?c) | ~bin(?b,?c)) ^ ?c = c1");
	PrintQuery(kb, "(~tin(?t,?c) | ~bin(?b,?c)) ^ c1 = ?c");
	PrintQuery(kb, "(~tin(?t,?c) | ~bin(?b,?c)) ^ c1 ~= ?c");
	PrintQuery(kb, "(~tin(?t,?c1) | ~bin(?b,?c2)) ^ ?c1 = ?c2");
	PrintQuery(kb, "(~tin(?t,?c1) | ~bin(?b,?c2)) ^ ?c1 ~= ?c2");
	
	PrintQuery(kb, "conn(?x,?y)");
	PrintQuery(kb, "conn@(?x,?y)"); // Transitive closure query
	//PrintQuery(kb, "true");
	//PrintQuery(kb, "false");
	//PrintQuery(kb, "~false");
	//PrintQuery(kb, "~~false");
	//PrintQuery(kb, "~(true^~(true ^ ~false))");
		
	System.out.println(kb);
    }
	
    public static void PrintQuery(GroundKb kb, String s) {
	System.out.println("\nQuery: " + s + ":\n" + 
			   kb.queryFOPCBindings(FOPC.parse(s)));
    }
	
    public static void Test3() {

	GroundKb kb = new GroundKb(null);

	kb.addFOPCFormula("(!E ?y Conn(?x,?y) ^ Conn(?y,?z)) => BConn(?x,?z)"); // Project
	// out
	// ?y
	kb.addFOPCFormula("Conn(1,2)");
	kb.addFOPCFormula("Conn(2,3)");
	kb.addFOPCFormula("Conn(3,4)");
	kb.addFOPCFormula("Conn(3,5)");
	kb.addFOPCFormula("Conn(3,5)"); // Duplicates removed!
	kb.addFOPCFormula("Univ(5)");

	System.out.println(kb);
	
	PrintQuery(kb, "Conn@(?x,?y)");
    }

    public static void QueryBindings(GroundKb kb, String query) {
	System.out.println("Query: " + query);
	System.out.println(kb.queryFOPCBindings(query));
    }

    public static void QueryTF(GroundKb kb, String query) {
	System.out.println("Query: " + query);
	System.out.println(kb.queryFOPC(query));
    }

    /////////////////////////////////////////////////////////////////////////
    //                    A very simple GroundDomain
    /////////////////////////////////////////////////////////////////////////

    public static class SimpleDomain implements GroundDomain {
	public int PRED_ID_COUNT = 0;
	public int TYPE_ID_COUNT = 0;
	public int INSTANCE_ID_COUNT = 0;
	public HashMap _hmPred2ID = new HashMap();  // FOPC.PNode -> Integer
	public HashMap _hmID2Pred = new HashMap();  // Integer -> FOPC.PNode
	public HashMap _hmType2ID = new HashMap();  // FOPC.PNode -> Integer
	public HashMap _hmID2Type = new HashMap();  // Integer -> FOPC.PNode
	public HashMap _hmInst2ID = new HashMap();  // FOPC.Term -> Integer
	public HashMap _hmID2Inst = new HashMap();  // Integer -> FOPC.Term
	public HashMap _hmPID2Slots = new HashMap(); // Integer -> IntArray of Type IDs
	public HashMap _hmPID2HSet  = new HashMap(); // Integer -> HashSet of IntArrays
	public HashMap _hmTID2IS    = new HashMap(); // Integer -> IntSet of Inst IDs  

	public IntSet _isFluents    = new IntSet(); // Ints representing fluent PIDs
	public IntSet _isNonFluents = new IntSet(); // Ints representing non-fluent PIDs

	public SimpleDomain() {	}
		
	public int addPredicate(FOPC.PNode pred) {
	    Integer pid = (Integer)_hmPred2ID.get(pred);
	    if (pid != null) return pid.intValue();
	    pid = new Integer(PRED_ID_COUNT++);
	    _hmPred2ID.put(pred, pid);
	    _hmID2Pred.put(pid, pred);
	    IntArray ia = new IntArray();
	    for (int i = 0; i < pred._nArity; i++) {
		ia.add(-1);
	    }
	    _hmPID2Slots.put(pid, ia);
	    _hmPID2HSet.put(pid, new HashSet());
	    return pid.intValue();
	}
		
	public int addType(FOPC.PNode type) {
	    Integer tid = (Integer)_hmType2ID.get(type);
	    if (tid != null) return tid.intValue();
	    if (type._nArity != 1) return -1;
	    tid = new Integer(TYPE_ID_COUNT++);
	    _hmType2ID.put(type, tid);
	    _hmID2Type.put(tid, type);
	    _hmTID2IS.put(tid, new IntSet());
	    return tid.intValue();
	}
		
	public int setPredSlotType(FOPC.PNode pred, int slot, FOPC.PNode type) {
	    Integer pid = (Integer)_hmPred2ID.get(pred);
	    Integer tid = (Integer)_hmType2ID.get(type);
	    if (pid == null || tid == null) return -1;
	    IntArray ia = (IntArray)_hmPID2Slots.get(pid);
	    if (slot >= ia.count) return -1;
	    ia.set(slot, tid.intValue());
	    return tid.intValue();
	}
		
	public int addTypeInstance(FOPC.PNode type, FOPC.Term inst) {
	    Integer tid = (Integer)_hmType2ID.get(type);
	    if (tid == null) return -1;
	    Integer iid = (Integer)_hmInst2ID.get(inst);
	    if (iid == null) {
		iid = new Integer(INSTANCE_ID_COUNT++);
		_hmInst2ID.put(inst, iid);
		_hmID2Inst.put(iid, inst);
	    }
	    IntSet is = (IntSet)_hmTID2IS.get(tid);
	    int ivalue = iid.intValue();
	    is.add(ivalue);
	    return ivalue;
	}

	// Adds or deletes based on polarity of PredBinding
	public boolean addPredBinding(FOPC.PNode pred, ArrayList inst_names) {
	    int pid = getPredID(pred);
	    if (pid == -1 || pred._nArity != inst_names.size()) {
		System.out.println("Error in addPredBinding: " + pred._sPredName + " " + 
				   inst_names + ": Incorrect arity [" + pred._nArity + 
				   "/" + inst_names.size() + "] or pid: " + pid); 
		return false;
	    }
	    IntArray ia = new IntArray();
	    for (int i = 0; i < pred._nArity; i++) {
		Integer iid = (Integer)_hmInst2ID.get(inst_names.get(i));
		if (iid == null) {
		    System.out.println("Error in addPredBinding: " + inst_names.get(i) +
				       " not found in instance store.");
		    return false;
		}
		int ivalue = iid.intValue();
		int tid = getPredSlotType(pid, i);
		if (!((IntSet)getTypeInstances(tid)).contains(ivalue)) {
		    System.out.println("Error in addPredBinding: Type mismatch: " + 
				       pred._sPredName + ": " + inst_names + ", slot: " + i);
		    return false;
		}
		ia.set(i, ivalue);
	    }
	    //System.out.println("Adding " + ia);

	    if (!pred._bIsNegated) {
		((HashSet)_hmPID2HSet.get(pid)).add(ia);
	    } else {
		((HashSet)_hmPID2HSet.get(pid)).remove(ia);
	    }
	    return true;
	}

	public void clearGroundAssertions() {
	    Iterator i = _hmPID2HSet.entrySet().iterator();
	    while (i.hasNext()) {
		Map.Entry me = (Map.Entry)i.next();
		((HashSet)me.getValue()).clear();
	    }
	}

	public void clearGroundAssertions(String pred, int arity) {
	    FOPC.PNode p = new FOPC.PNode(false, pred);
	    p._nArity = arity;
	    int pid = getPredID(p);
	    if (pid < 0) System.out.println("ERROR clear ground assertions: " + pred + " = " + pid);
	    ((HashSet)_hmPID2HSet.get(new Integer (pid))).clear();
	}
		
	public boolean isFluentPID(int pid) {
	    return _isFluents.contains(pid);
	}

	public boolean isNonFluentPID(int pid) {
	    return _isNonFluents.contains(pid);
	}

	// Use to mark specifically as fluent or non-fluenta
	public void markAsFluent(String pred, int arity, boolean is_fluent) {

	    FOPC.PNode p = new FOPC.PNode(false, pred);
	    p._nArity = arity;
	    int pid = getPredID(p);
	    if (pid < 0) System.out.println("ERROR clear ground assertions: " + pred + " = " + pid);
	    if (is_fluent) {
		_isFluents.add(pid);
	    } else {
		_isNonFluents.add(pid);
	    }
	}
	
	public void clearGroundFluents() {
	    for (int i = 0; i < _isFluents.count; i++) {
		((HashSet)_hmPID2HSet.get(new Integer(_isFluents.l[i]))).clear();
	    }
	}

	public int getPredID(FOPC.PNode pred) {
	    pred = (FOPC.PNode)pred.copy();
	    pred._alTermBinding.clear();
	    pred._bIsNegated = false;
	    Integer i = (Integer)_hmPred2ID.get(pred);
	    return (i == null ? -1 : i.intValue());
	}
		
	public int getInstanceID(FOPC.Term inst) {
	    Integer i = (Integer)_hmInst2ID.get(inst);
	    return (i == null ? -1 : i.intValue());
	}
		
	public FOPC.PNode getPredName(int id) {
	    return (FOPC.PNode)_hmID2Pred.get(new Integer(id));
	}
		
	public FOPC.PNode getTypeName(int id) {
	    return (FOPC.PNode)_hmID2Type.get(new Integer(id));
	}
		
	public int getPredSlotType(int pred_id, int slot) {
	    IntArray ia = (IntArray)_hmPID2Slots.get(new Integer(pred_id));
	    if (slot >= ia.count) return -1;
	    return ia.l[slot];
	}
		
	public FOPC.Term getInstanceName(int id) {
	    return (FOPC.Term)_hmID2Inst.get(new Integer(id));
	}
		
	public IntSet getTypeInstances(int type) {
	    return (IntSet)_hmTID2IS.get(new Integer(type));
	}
		
	public HashSet getPredBindings(int pred) {
	    return (HashSet)_hmPID2HSet.get(new Integer(pred));
	}
		
	public ArrayList getTerms(IntArray terms) {
	    ArrayList al = new ArrayList();
	    for (int i = 0; i < terms.count; i++) {
		int inst_id = terms.l[i];
		FOPC.Term t = (FOPC.Term)_hmID2Inst.get(new Integer(inst_id));
		al.add(t);
	    }
	    return al;
	}
		
	public ArrayList getTerms(IntSet terms) {
	    ArrayList al = new ArrayList();
	    for (int i = 0; i < terms.count; i++) {
		int inst_id = terms.l[i];
		FOPC.Term t = (FOPC.Term)_hmID2Inst.get(new Integer(inst_id));
		al.add(t);
	    }
	    return al;
	}
		
	public String printTerms(IntArray terms) {
	    StringBuffer sb = new StringBuffer();
	    for (int i = 0; i < terms.count; i++) {
		int inst_id = terms.l[i];
		FOPC.Term t = (FOPC.Term)_hmID2Inst.get(new Integer(inst_id));
		sb.append((i > 0 ? ", " : " ") + t.toString());
	    }
	    return sb.toString();
	}
		
	public String printTerms(IntSet terms) {
	    StringBuffer sb = new StringBuffer();
	    for (int i = 0; i < terms.count; i++) {
		int inst_id = terms.l[i];
		FOPC.Term t = (FOPC.Term)_hmID2Inst.get(new Integer(inst_id));
		sb.append((i > 0 ? ", " : " ") + t.toString());
	    }
	    return sb.toString();
	}

	// Here all types assumed disjoint
	public int getTypeJoin(int tid_1, int tid_2) {
	    if (tid_1 != tid_2) {
		return -1;
	    } else {
		return tid_1;
	    }
	}
		
	public String toString() {
			
	    StringBuffer sb = new StringBuffer();
			
	    // Print out types and instances
	    sb.append("Types:\n------\n");
	    Iterator i = _hmID2Type.keySet().iterator();
	    while (i.hasNext()) {
		Integer type_id = (Integer)i.next();
		FOPC.PNode type = (FOPC.PNode)_hmID2Type.get(type_id);
		sb.append("ID: " + type_id + " " + (type != null ? type._sPredName : type) + " = {");
		IntSet is = (IntSet)_hmTID2IS.get(type_id);
		sb.append(printTerms(is) + " }\n");
	    }
			
	    // Print out predicates and slot types
	    sb.append("\nPredicates:\n-----------");
	    i = _hmID2Pred.keySet().iterator();
	    while (i.hasNext()) {
				
				// Print out predicate name and slot info
		Integer pred_id = (Integer)i.next();
		FOPC.PNode pred = (FOPC.PNode)_hmID2Pred.get(pred_id);
		sb.append("\nID: " + pred_id + " " + (pred != null ? pred._sPredName : pred) + "(");
		IntArray ia = (IntArray)_hmPID2Slots.get(pred_id);
		for (int slot = 0; slot < pred._nArity; slot++) {
		    int type_id = ia.l[slot];
		    FOPC.PNode type = getTypeName(type_id);
		    sb.append((slot > 0 ? "," : "") + (type != null ? type._sPredName : type));
		}
		sb.append(")\n");
				
				// Print out ground instances
		HashSet ts = getPredBindings(pred_id.intValue());
		Iterator gi = ts.iterator();
		while (gi.hasNext()) {
		    ia = (IntArray)gi.next();
		    sb.append("  - [" + printTerms(ia) + " ]\n");
		}
	    }
	    return sb.toString();
	}
    }
	
}
