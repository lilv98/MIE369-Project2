//////////////////////////////////////////////////////////////////////
//
// First-Order Logic Package
//
// Class:  ClauseKb
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   7/25/03
//
// NOTES:
// ------
// - Have managed to avoid redundant clauses by using a lexical ordering
//   for ConnNodes (see ReorderPNodes) and by always resetting variables
//   to start at 1 when standardizing apart for unification and when
//   generating the resulting clauses (reset counter to 1).  Seems to
//   catch the majority of redundant clauses.  Also introduced
//   standardizeApartClause to pay more attention to getting substitutions
//   in increasing variable id order from left to right of clauses.
//
// TODO:
// -----
// - Keep track of derivations (proof tracking).
// - Get rid of subsumed clauses (disjunctive MSS/MGS technique?).
// - Heuristics for throwing out unresolvable clauses, avoiding disconnected
//   parts of graph.
// - Lots of room for efficiency improvement.  Too much String processing,
//   redundant work, and error checking.
//////////////////////////////////////////////////////////////////////

package logic.kb.fol;

import java.io.*;
import java.util.*;

import graph.*;
import logic.kb.*;
import logic.kb.fol.parser.*;

public class ClauseKb extends Kb {

	// Print resolutions as they are made?
	public static final boolean PRINT_RESOLUTIONS = false;

	public static final boolean PRINT_ELIMINATION_STEP = false;

	public static final boolean PRINT_ADDED_FORMULA = false;

	public static final boolean PRINT_MAX_RES = false;

	public static final boolean PRINT_CNF = false;

	public static boolean GEN_GRAPH = false;

	public static final boolean COLLECT_ONLY_CONSTANTS = true;

	public static final boolean MAINTAIN_PROOFS = false; // true;

	public static final boolean PRINT_PROOFS = false; // true;

	public static final boolean PRINT_FIRST_PROOF_ONLY = false; // true;

	public static final String QUERY = "QUERY";

	// For the timer
	public static long _lTime;

	public HashMap _hmProofs; // Tracks all derivations

	public HashMap _hmPred2Clause; // Pred is a String (name_arity)

	public HashMap _hmPred2Name; // Maps name_arity -> name

	public HashMap _hmPred2Arity; // Maps name_arity -> arity

	public List _lElimOrdering; // Ordering of predicates (as Strings:
								// name_arity)

	public Graph _graphClauses; // A graph of connectivity b/w predicates due to
								// clauses

	public BindingSet _bs; // Store query results

	public boolean ALL_PROOFS; // Retrieve one proof or all proofs (for getting
								// query bindings)

	public int MAX_RES_PER_ELIM; // In case of infinite resolvents

	public ArrayList _alQueryBindings;

	public int _nResSteps;

	public float _fQueryTime;

	public String _sQueryFile;

	public ClauseKb() {
		this(100);
	}

	public ClauseKb(int max_res) {
		_hmPred2Clause = new HashMap();
		_hmPred2Name = new HashMap();
		_hmPred2Arity = new HashMap();
		_hmProofs = null;
		_lElimOrdering = null;
		_graphClauses = null;
		_bs = null;
		_alQueryBindings = null;
		ALL_PROOFS = false;
		MAX_RES_PER_ELIM = /* max_res; */100;
	}

	// ///////////////////////////////////////////////////////////////////////////
	// Kb Interface
	// ///////////////////////////////////////////////////////////////////////////

	public void setQueryFile(String file) {
		_sQueryFile = file;
	}

	public float getQueryTime() {
		return _fQueryTime;
	}

	public int getNumInfClauses() {
		return _nResSteps;
	}

	public int getProofLength() {
		return -1; // _nProofSteps;
	}

	// Convert a first-order formula to clauses and add to kb
	public void addFOPCFormula(String s) {
		addFormula(_hmPred2Clause, s);
	}

	public void addFOPCFormula(FOPC.Node n) {
		addFormula(_hmPred2Clause, n);
	}

	// Query to see if kb entails s (false only implies could not be proven)
	public boolean queryFOPC(String query) {
		return queryFOPC(FOPC.parse(query));
	}

	public boolean queryFOPC(FOPC.Node n) {
		ALL_PROOFS = false;
		if (MAINTAIN_PROOFS) {
			_hmProofs = new HashMap();
		}
		FOPC.Node temp_query = n.copy().convertNNF(true);
		HashMap new_clauses = copyClauseMap(_hmPred2Clause);
		addFormula(new_clauses, temp_query);
		boolean ref_found = canRefute(new_clauses);

		// Print proofs?
		if (PRINT_PROOFS) {
			printProofs(new FOPC.TNode(false));
		}

		return ref_found;
	}

	public boolean queryFOPC(String assume, String query) {
		System.out
				.println("DLFOLClauseKB: queryFOPC(String,String) not implemented.");
		// System.exit(1);
		return false;
	}

	public boolean queryFOPC(FOPC.Node assume, FOPC.Node query) {
		System.out
				.println("DLFOLClauseKB: queryFOPC(String,String) not implemented.");
		// System.exit(1);
		return false;
	}

	public BindingSet queryFOPCBindings(String query) {
		return queryFOPCBindings(FOPC.parse(query));
	}

	// Query for bindings of free vars
	public BindingSet queryFOPCBindings(FOPC.Node query) {

		// Set up the binding set, query implication, query node, binding vars
		ALL_PROOFS = true;
		if (MAINTAIN_PROOFS) {
			_hmProofs = new HashMap();
		}
		_bs = new BindingSet();
		HashMap new_clauses = copyClauseMap(_hmPred2Clause);
		query.setFreeVars();
		Set free_vars = query._hsFreeVarsOut;
		_hmPred2Arity.put(QUERY, new Integer(free_vars.size()));
		FOPC.PNode query_node = new FOPC.PNode(false, QUERY);
		Iterator i = free_vars.iterator();
		_alQueryBindings = new ArrayList();
		while (i.hasNext()) {
			FOPC.TVar qvar = (FOPC.TVar) i.next();
			query_node.addBinding(qvar);
			_alQueryBindings.add(qvar);
			_bs.addVar(qvar.toString());
		}
		FOPC.Node imp_node = new FOPC.ConnNode(FOPC.ConnNode.IMPLY, query,
				query_node);
		FOPC.Node query_neg = query_node.copy().convertNNF(true);
		// System.out.println("Query imp: " + imp_node.toFOLString());
		// System.out.println("Query neg: " + query_neg.toFOLString());

		// Now add the additional clauses and complete the proof
		addFormula(new_clauses, imp_node);
		addFormula(new_clauses, query_neg);
		canRefute(new_clauses);
		ALL_PROOFS = false;

		// Print proofs?
		if (PRINT_PROOFS) {
			printProofs(new FOPC.TNode(false));
		}

		return _bs.seal();
	}

	public BindingSet queryFOPCBindings(String assume, String query) {
		System.out
				.println("DLFOLClauseKB: queryFOPCBindings(String,String) not implemented.");
		// System.exit(1);
		return null;
	}

	public BindingSet queryFOPCBindings(FOPC.Node assume, FOPC.Node query) {
		System.out
				.println("DLFOLClauseKB: queryFOPCBindings(String,String) not implemented.");
		// System.exit(1);
		return null;
	}

	// ///////////////////////////////////////////////////////////////////////////

	public void setOrdering() {
		setOrdering(_hmPred2Clause);
	}

	public void setOrdering(HashMap hm) {
		setOrdering(hm, "tp.dot");
	}

	public void setOrdering(String filename) {
		setOrdering(_hmPred2Clause, filename);
	}

	public void setOrdering(HashMap hm, String filename) {

		// First, build the connectivity graph
		_graphClauses = new Graph(false);
		Iterator i = hm.entrySet().iterator();

		// Go through each set of clauses
		List free_vars = new ArrayList(hm.keySet());
		Set factors = new HashSet();
		while (i.hasNext()) {
			Map.Entry me = (Map.Entry) i.next();
			String key = (String) me.getKey();
			ClauseList cl = (ClauseList) me.getValue();

			// Add pos clauses
			Iterator j = cl._alPosClauses.iterator();
			while (j.hasNext()) {
				FOPC.Node n = (FOPC.Node) j.next();
				if (n instanceof FOPC.ConnNode) {
					ArrayList al = new ArrayList();
					FOPC.ConnNode c = (FOPC.ConnNode) n;
					Iterator k = c._alSubNodes.iterator();
					while (k.hasNext()) {
						FOPC.PNode p = (FOPC.PNode) k.next();
						al.add(p._sPredName + "_" + p._nArity);
					}
					// System.out.println("Adding all pair links: " + al);
					_graphClauses.addAllPairLinks(al);
					factors.add(new HashSet(al));
				} else {
					System.out.println("Error in pos clause list: "
							+ n.toFOLString());
					System.exit(1);
				}
			}

			// Add neg clauses
			j = cl._alNegClauses.iterator();
			while (j.hasNext()) {
				FOPC.Node n = (FOPC.Node) j.next();
				if (n instanceof FOPC.ConnNode) {
					ArrayList al = new ArrayList();
					FOPC.ConnNode c = (FOPC.ConnNode) n;
					Iterator k = c._alSubNodes.iterator();
					while (k.hasNext()) {
						FOPC.PNode p = (FOPC.PNode) k.next();
						al.add(p._sPredName + "_" + p._nArity);
					}
					_graphClauses.addAllPairLinks(al);
					factors.add(new HashSet(al));
				} else {
					System.out.println("Error in neg clause list: "
							+ n.toFOLString());
					System.exit(1);
				}
			}
		}

		// Now, get a low width ordering
		if (GEN_GRAPH) {
			_graphClauses.genDotFile(filename);
		}
		_lElimOrdering = _graphClauses.greedyTWSort(free_vars, factors);
		if (_alQueryBindings != null) {
			String query_str = QUERY + "_" + _alQueryBindings.size();
			_lElimOrdering.remove(query_str);
			_lElimOrdering.add(query_str);
		}
		// System.out.println("Ordering: " + _lElimOrdering);
		// System.out.println("Binary Tree Width: " +
		// _graphClauses._df.format(_graphClauses._dMaxBinaryWidth));
	}

	// Returns true if kb inconsistent (will modify clauses so should be a
	// copy!)
	public boolean canRefute() {
		return canRefute(copyClauseMap(_hmPred2Clause));
	}

	public boolean canRefute(HashMap clauses) {

		// System.out.println("\nTrying to refute: \n" + printClauses(clauses));
		_nResSteps = 0;

		// First determine an elimination order (important if new predicates
		// added)
		if (_lElimOrdering == null
				|| !clauses.keySet().equals(new HashSet(_lElimOrdering))) {
			// System.out.println("keySet: " + clauses.keySet());
			// System.out.println("elimOrder: " + _lElimOrdering);
			setOrdering(clauses);
		}

		// Now, go through each predicate in order, resolve, and eliminate
		ResetTimer();
		Iterator i = _lElimOrdering.iterator();
		while (i.hasNext()) {
			String pred = (String) i.next();

			// If a refutation is found, immediately return
			boolean ref_found = performElimStep(clauses, pred);
			if (ref_found) {
				_fQueryTime = (float) GetElapsedTime();
				return true;
			}
		}

		_fQueryTime = (float) GetElapsedTime();
		return false; // No refutation found
	}

	// Remove all clauses with pred from 'clauses', resolve them
	// together and discard remaining ones with pred, add new clauses
	// back to 'clauses'. Return true if a refutation was found.
	//
	// Note: pred here is predname_arity
	public boolean performElimStep(HashMap clauses, String pred) {

		boolean found_refutation = false;

		String predname = (String) _hmPred2Name.get(pred);
		int arity = ((Integer) _hmPred2Arity.get(pred)).intValue();

		// Get ClauseList (pos/neg clauses) for pred being eliminated... clone
		// so that we can remove all of these clauses from the main list
		// of clauses below.
		ClauseList cl = (ClauseList) getClauseList(clauses, pred, false)
				.clone();
		if (cl == null) {
			return found_refutation;
		}

		// Remove all mention of clauses being resolved here in the main
		// set of clauses since we are eliminating this predicate from the
		// clauses and will put all of the resolvents here in place of them.
		Iterator j = cl._alPosClauses.iterator();
		while (j.hasNext()) {
			removeFromClauseLists(clauses, (FOPC.Node) j.next());
		}
		j = cl._alNegClauses.iterator();
		while (j.hasNext()) {
			removeFromClauseLists(clauses, (FOPC.Node) j.next());
		}

		// Now get a list of resolvents after pred eliminated
		if (PRINT_ELIMINATION_STEP) {
			System.out.println("--------------------------------------");
			System.out.println("ClauseList for " + pred + ":\n" + cl);
			System.out.println("--------------------------------------");
			System.out.print("Eliminating " + pred + "...");
		}
		// System.out.println("New clause list: \n" + printClauses(clauses));
		Set s = elimPred(predname, arity, cl);
		// System.out.println("Eliminated " + predname + " -> " + s);
		if (PRINT_ELIMINATION_STEP) {
			System.out.println(" -> " + s.size() + " resolvents");
		}

		// Check for TNode of false in return values, otherwise add resolvents
		// back into clause lists.
		j = s.iterator();
		while (j.hasNext()) {
			FOPC.Node n = (FOPC.Node) j.next();
			if (n instanceof FOPC.TNode) {
				if (((FOPC.TNode) n)._bValue) {
					System.out.println("Should not get true TNode during res!");
					System.exit(1);
				} else {
					if (ALL_PROOFS) {
						found_refutation = true;
					} else {
						return true; // Refutation found, don't need all
										// proofs!
					}
				}
			} else if (n instanceof FOPC.ConnNode) {
				addToClauseLists(clauses, n);
			} else {
				System.out.println("Illegal FOPC.Node durign res: "
						+ n.toFOLString());
				System.exit(1);
			}
		}

		return found_refutation;
	}

	// Resolve clauses over predicate and return new list (minus predicate!)
	public Set elimPred(String predname, int arity, ClauseList cl) {

		HashSet res_set = new HashSet();
		Set return_set = new HashSet();
		int num_res = 0;

		// cl is a clone so we can modify it
		int prev_sz;
		do {
			prev_sz = cl.getNumClauses();

			// Iterate through all pos clauses
			// System.out.println("CLAUSE LISTS: \n" + cl);
			for (int pos_it = 0; pos_it < cl._alPosClauses.size(); pos_it++) {
				FOPC.ConnNode n1 = (FOPC.ConnNode) cl._alPosClauses.get(pos_it);

				// Iterator through all neg clauses
				for (int neg_it = 0; neg_it < cl._alNegClauses.size(); neg_it++) {
					FOPC.ConnNode n2 = (FOPC.ConnNode) cl._alNegClauses
							.get(neg_it);
					FOPC.NodePair p = new FOPC.NodePair(n1, n2);

					// Have we performed this resolution already? **This is key
					// to
					// efficiency because it compares the actual standardized
					// clauses
					// to see if they've been resolved against each other
					// before.
					if (!res_set.contains(p)) {
						res_set.add(p);

						// Determine all possible resolutions of n1, n2 over
						// pred
						int sz1 = n1._alSubNodes.size();
						for (int pos1 = 0; pos1 < sz1; pos1++) {
							FOPC.PNode p1 = (FOPC.PNode) n1._alSubNodes
									.get(pos1);
							if (p1._nArity != arity
									|| p1._bIsNegated
									|| !("" + p1._sPredName).equals(""
											+ predname)) {
								continue;
							}
							int sz2 = n2._alSubNodes.size();
							for (int pos2 = 0; pos2 < sz2; pos2++) {
								FOPC.PNode p2 = (FOPC.PNode) n2._alSubNodes
										.get(pos2);
								if (p2._nArity != arity
										|| !p2._bIsNegated
										|| !("" + p2._sPredName).equals(""
												+ predname)) {
									continue;
								}

								// These two match, so try to resolve
								if (PRINT_RESOLUTIONS) {
									System.out.print("Resolving "
											+ n1.toFOLString() + " [" + pos1
											+ "] " + ", " + n2.toFOLString()
											+ " [" + pos2 + "] ");
								}
								FOPC.Node res = resolveClauses(n1, pos1, n2,
										pos2);

								// Add to correct lists
								if (res == null) {
									if (PRINT_RESOLUTIONS) {
										System.out
												.println(" -> Could not unify!\n");
									}
									continue;
								}
								// Keep track of proof
								if (MAINTAIN_PROOFS
										&& (!(res instanceof FOPC.TNode) || !((FOPC.TNode) res)._bValue)) {
									addProofStep(n1, n2, res);
								}
								_nResSteps++;

								if (PRINT_RESOLUTIONS) {
									System.out.println(" -> "
											+ res.toFOLString() + "\n");
								}
								if (res instanceof FOPC.ConnNode) {
									int sz3 = ((FOPC.ConnNode) res)._alSubNodes
											.size();
									boolean contains_pred = false;
									for (int pos3 = 0; pos3 < sz3; pos3++) {
										FOPC.PNode p3 = (FOPC.PNode) ((FOPC.ConnNode) res)._alSubNodes
												.get(pos3);
										if (p3._nArity == arity
												&& // A quick hack!
												("" + p3._sPredName).equals(""
														+ predname)) {
											contains_pred = true;
											if (p3._bIsNegated) {
												if (!Contains(cl._alNegClauses,
														res)) {
													cl._alNegClauses.add(res);
												}
											} else {
												if (!Contains(cl._alPosClauses,
														res)) {
													cl._alPosClauses.add(res);
												}
											}
										}
									}
									// Only add to return set if it does not
									// contain current
									// predicate being eliminated
									if (!contains_pred) {
										return_set.add(res);
									}
								} else {
									if (!((FOPC.TNode) res)._bValue) {
										return_set.add(res);
										if (!ALL_PROOFS) {
											return return_set; // Can exit
																// early if only
																// need one
																// proof
										}
									} else {
										// A true TNode, don't add it (does not
										// refute anything!)
										// System.out.println("Tautology in
										// resolution: " + res);
										// System.exit(1);
									}
								}
								num_res++;
								if (num_res >= MAX_RES_PER_ELIM) {
									if (PRINT_MAX_RES) {
										System.out
												.println("...MAX_RES reached, continuing with next "
														+ "elimination step...");
									}
									return return_set;
								}
							}
						}
					} // else {
					// System.out.println("Already resolved: " + p);
					// }
				}
			}
		} while (cl.getNumClauses() > prev_sz);

		return return_set;
	}

	// Find resolvent of two clauses by unifying and eliminating the
	// respective positions (pos1, pos2 passed as arguments).
	// Makes sure duplicates are removed from resolved clause.
	// Return null if no unification possible.
	// Note: unify will standardize apart!
	public FOPC.Node resolveClauses(FOPC.ConnNode c1, int pos1,
			FOPC.ConnNode c2, int pos2) {

		// Don't resolve a clause with itself
		if (c1.equals(c2)) {
			return null;
		}

		// Copy clauses so unification does not corrupt other versions
		c1 = (FOPC.ConnNode) c1.copy();
		c2 = (FOPC.ConnNode) c2.copy();
		FOPC.PNode p1 = (FOPC.PNode) c1._alSubNodes.get(pos1);
		FOPC.PNode p2 = (FOPC.PNode) c2._alSubNodes.get(pos2);

		// ERROR Check
		// if (!p1._sPredName.equals(p2._sPredName) || p1._nArity != p2._nArity
		// ||
		// p1._bIsNegated == p2._bIsNegated) {
		// System.out.println("CANNOT RESOLVE: " + p1.toFOLString() +
		// " with " + p2.toFOLString());
		// System.exit(1);
		// }

		// Always standardize apart clauses before unification (reset var count
		// first)
		FOPC.TVar._nVarCount = 0;
		HashMap theta1 = FOPC.standardizeApartClause(c1);
		HashMap theta2 = FOPC.standardizeApartClause(c2);
		c1.substitute(theta1);
		c2.substitute(theta2);

		// Ensure that we don't need to standardize apart (i.e., shared
		// variables)
		// ... should have already been done
		boolean share_vars = false;
		p1.setFreeVars();
		p2.setFreeVars();
		Iterator it = p1._hsFreeVarsOut.iterator();
		while (it.hasNext() && !share_vars) {
			share_vars = p2._hsFreeVarsOut.contains(it.next());
		}
		if (share_vars) {
			System.out.println("Should never reach!");
			System.out.println(p1.toString());
			System.out.println(p2.toString());
			theta1 = FOPC.standardizeApartClause(c1);
			theta2 = FOPC.standardizeApartClause(c2);
			c1.substitute(theta1);
			c2.substitute(theta2);
			System.exit(1);
		}

		// Unify on the specified predicates
		HashMap theta = FOPC.unify(p1, p2);
		if (theta == null) {
			return null;
		}
		// System.out.println("Before sub: " + c1.toFOLString() + ", " +
		// c2.toFOLString());
		c1.substitute(theta);
		c2.substitute(theta);
		// System.out.println("After sub: " + c1.toFOLString() + ", " +
		// c2.toFOLString());

		// Make new unified clause without resolved PNodes
		if (c1._alSubNodes.size() == 1 && c2._alSubNodes.size() == 1) {

			// ///////////////////////////////////////////////////////////////////////
			// Add query bindings if found
			// ///////////////////////////////////////////////////////////////////////
			if (_bs != null
					&& ((FOPC.PNode) c1._alSubNodes.get(0))._sPredName == QUERY) {

				// Add bindings to binding set if we are querying for free vars
				Iterator ans_it = ((FOPC.PNode) c1._alSubNodes.get(0))._alTermBinding
						.iterator();
				Iterator bind_it = _alQueryBindings.iterator();

				// The following determines whether to actually add this answer
				boolean collect = true;
				if (COLLECT_ONLY_CONSTANTS) {
					while (ans_it.hasNext()) {
						FOPC.Term ans_term = (FOPC.Term) ans_it.next();
						if (ans_term instanceof FOPC.TVar) {
							collect = false;
						} else if (ans_term instanceof FOPC.TFunction) {
							// May want to keep generic functions
							if (((FOPC.TFunction) ans_term)._nArity > 0) {
								collect = false;
							}
						}
					}
					// Reset iterator
					ans_it = ((FOPC.PNode) c1._alSubNodes.get(0))._alTermBinding
							.iterator();
				}

				if (collect) {
					int entry = _bs.makeNewBindingEntry();
					while (ans_it.hasNext()) {
						FOPC.TVar bind_var = (FOPC.TVar) bind_it.next();
						FOPC.Term ans_term = (FOPC.Term) ans_it.next();
						_bs.addBinding(entry, bind_var.toString(), ans_term
								.toString());
					}
				}
			}
			// ///////////////////////////////////////////////////////////////////////

			return new FOPC.TNode(false); // Must resolve to empty set!
		}
		HashSet already_added = new HashSet(); // Check for duplicates and
												// remove!
		FOPC.ConnNode ret = new FOPC.ConnNode(FOPC.ConnNode.OR);

		// Add nodes from clause 1
		int sz1 = c1._alSubNodes.size();
		for (int pc1 = 0; pc1 < sz1; pc1++) {
			FOPC.Node to_add = (FOPC.Node) c1._alSubNodes.get(pc1);
			if (pc1 != pos1 && !already_added.contains(to_add)) {
				ret.addSubNode(to_add);
				already_added.add(to_add);
			}
		}

		// Add nodes from clause 2
		int sz2 = c2._alSubNodes.size();
		for (int pc2 = 0; pc2 < sz2; pc2++) {
			FOPC.Node to_add = (FOPC.Node) c2._alSubNodes.get(pc2);
			if (pc2 != pos2 && !already_added.contains(to_add)) {
				ret.addSubNode(to_add);
				already_added.add(to_add);
			}
		}

		// Note: this can be much more efficient... nodes which disjoin to prove
		// TRUE
		// are filtered here but we can really return upon first found!
		// Now filter for tautological subclauses - i.e. remove subsumed clauses
		if (tautology(ret)) {
			return (new FOPC.TNode(true));
		}

		// ERROR Check
		// if (ret._alSubNodes.size() != (c1._alSubNodes.size() +
		// c2._alSubNodes.size() - 2)) {
		// System.out.println("SIZE MISMATCH");
		// System.out.println(" - " + c1.toFOLString() + " " + pos1);
		// System.out.println(" - " + c2.toFOLString() + " " + pos2);
		// System.out.println(" " + theta);
		// System.out.println(" --> " + ret.toFOLString());
		// //System.exit(1);
		// }

		// Try to make into a canonical form
		ReorderPNodes(ret);
		FOPC.TVar._nVarCount = 0;
		HashMap subst = FOPC.standardizeApartClause(ret);
		ret.substitute(subst);

		return ret;
	}

	// Filters complementary PNodes - was changed to just detect tautology
	public boolean tautology(FOPC.ConnNode c) {
		ArrayList pnodes = new ArrayList();
		Iterator i = c._alSubNodes.iterator();
		while (i.hasNext()) {
			FOPC.Node n = (FOPC.Node) i.next();
			if (n instanceof FOPC.PNode) {
				pnodes.add(n);
			}
		}

		// Now, for each pnode that does not cancel with another
		// pnode, add it to the ret_nodes.
		for (int j = 0; j < pnodes.size(); j++) {
			FOPC.PNode pj = (FOPC.PNode) pnodes.get(j);
			FOPC.PNode pjc = null;
			for (int k = 0; /* !neg_match_found && */k < pnodes.size(); k++) {
				FOPC.PNode pk = (FOPC.PNode) pnodes.get(k);
				FOPC.PNode pkc = null;
				if (((pj._sPredName == null && pk._sPredName == null && pj._nPredID == pk._nPredID) || (pj._sPredName != null && pj._sPredName
						.equals("" + pk._sPredName)))
						&& pj._nArity == pk._nArity
						&& pj._bIsNegated == !pk._bIsNegated) {

					// Generate standardized apart nodes (not sure if we have
					// to!)
					if (pjc == null) {
						pjc = (FOPC.PNode) pj.copy();
						pjc.substitute(FOPC.standardizeApartNode(pjc));
					}
					if (pkc == null) {
						pkc = (FOPC.PNode) pk.copy();
						pkc.substitute(FOPC.standardizeApartNode(pkc));
					}

					// Now test if terms can be unified
					if (FOPC.unify(pjc, pkc) != null) {
						return true;
					}
					// neg_match_found = true;
					// for (int m = 0; neg_match_found && m < pj._nArity; m++) {
					// neg_match_found =
					// pj._alTermBinding.get(m).equals(pk._alTermBinding.get(m));
					// }
				}
			}
		}

		// if (!ret_nodes.equals(l)) {
		// System.out.println("Before: " + l);
		// System.out.println("After: " + ret_nodes);
		// }

		return false;
	}

	public void addFormula(HashMap hm, String s) {

		if (PRINT_ADDED_FORMULA) {
			System.out.println("Adding formula: " + s);
		}
		addFormula(hm, FOPC.parse(s));
	}

	public void addFormula(FOPC.Node n) {
		addFormula(_hmPred2Clause, n);
	}

	public void addFormula(HashMap hm, FOPC.Node n) {

		// DNF conversion to push down quantifiers is pointless here
		// since we'll get rid of EXISTS and CNF(DNF) will yield
		// an exponential blowup with simplification.
		boolean SAVED_ALLOW_DNF = FOPC.ALLOW_DNF;
		FOPC.ALLOW_DNF = false;

		// Simpify n and convert to NNF
		// System.out.println(n.toFOLString());
		n = n.copy(); // Following functions may modify original!
		n = FOPC.simplify(n);
		n = FOPC.skolemize(n);
		n = FOPC.convertCNF(n);

		// Break apart top-level, standardize apart free vars, and add to clause
		// list
		if ((n instanceof FOPC.ConnNode)
				&& ((FOPC.ConnNode) n)._nType == FOPC.ConnNode.AND) {

			// Go through all subclauses
			Iterator i = ((FOPC.ConnNode) n)._alSubNodes.iterator();
			while (i.hasNext()) {
				FOPC.Node sn = (FOPC.Node) i.next();

				// Reality check!
				if (!(((sn instanceof FOPC.ConnNode) && ((FOPC.ConnNode) sn)._nType == FOPC.ConnNode.OR) || (sn instanceof FOPC.PNode))) {

					System.out.println("CNF conversion was bad!");
					System.exit(1);
				}

				if (sn instanceof FOPC.PNode) {
					FOPC.ConnNode cn = new FOPC.ConnNode(FOPC.ConnNode.OR);
					cn.addSubNode(sn);
					if (PRINT_CNF) {
						System.out.println("CNF: " + cn);
					}
					ReorderPNodes(cn);
					addToClauseLists(hm, cn);
				} else {
					if (PRINT_CNF) {
						System.out.println("CNF: " + sn);
					}
					ReorderPNodes((FOPC.ConnNode) sn);
					addToClauseLists(hm, sn);
				}
			}

		} else {
			if (!(((n instanceof FOPC.ConnNode) && ((FOPC.ConnNode) n)._nType == FOPC.ConnNode.OR) || (n instanceof FOPC.PNode))) {

				System.out.println("CNF conversion was bad!");
				System.exit(1);
			}

			if (n instanceof FOPC.PNode) {
				FOPC.ConnNode cn = new FOPC.ConnNode(FOPC.ConnNode.OR);
				cn.addSubNode(n);
				if (PRINT_CNF) {
					System.out.println("CNF: " + cn);
				}
				ReorderPNodes(cn);
				addToClauseLists(hm, cn);
			} else {
				if (PRINT_CNF) {
					System.out.println("CNF: " + n);
				}
				ReorderPNodes((FOPC.ConnNode) n);
				addToClauseLists(hm, n);
			}
		}

		// Restore DNF conversion
		FOPC.ALLOW_DNF = SAVED_ALLOW_DNF;
	}

	public String toString() {
		return "ClauseKb";
	}
	
	public String showKbContents() {
		return printClauses(_hmPred2Clause);
	}

	public String printClauses(HashMap hm) {
		StringBuffer sb = new StringBuffer();
		Iterator i = hm.entrySet().iterator();
		while (i.hasNext()) {
			Map.Entry me = (Map.Entry) i.next();
			sb.append("**" + me.getKey() + "**:\n" + me.getValue() + "\n");
		}
		return sb.toString();
	}

	// ////////////////////////////////////////////////////////////////////////
	// Keep track of the clause lists
	// ////////////////////////////////////////////////////////////////////////

	public void printProofs(FOPC.Node n) {
		printProofs(n, 0, new HashSet());
	}

	public void printProofs(FOPC.Node n, int sz, HashSet shown) {

		indent(sz++);
		System.out.print("- " + n.toFOLString());
		if (shown.contains(n)) {
			System.out.println(" <- [ALREADY SHOWN]");
			return;
		}
		shown.add(n);
		Set s = getNodeProofs(n, false);
		if (s == null) {
			System.out.println(" <- [GIVEN]");
		} else {
			Iterator i = s.iterator();
			while (i.hasNext()) {
				FOPC.NodePair np = (FOPC.NodePair) i.next();
				System.out.println(" <- ");
				printProofs(np._n1, sz, shown);
				printProofs(np._n2, sz, shown);
				if (PRINT_FIRST_PROOF_ONLY) {
					break;
				}
			}
		}
	}

	public void indent(int l) {
		for (int i = 0; i < l; i++) {
			System.out.print("   ");
		}
	}

	public void addProofStep(FOPC.Node n1, FOPC.Node n2, FOPC.Node res) {
		Set s = getNodeProofs(res, true);
		s.add(new FOPC.NodePair(n1, n2));
	}

	public Set getNodeProofs(FOPC.Node res, boolean create) {
		Set s = (Set) _hmProofs.get(res);
		if (s == null && create) {
			s = new HashSet();
			_hmProofs.put(res, s);
		}
		return s;
	}

	// ////////////////////////////////////////////////////////////////////////
	// Keep track of the clause lists
	// ////////////////////////////////////////////////////////////////////////

	public HashMap copyClauseMap(HashMap hm) {
		HashMap ret = new HashMap();
		Iterator i = hm.entrySet().iterator();
		while (i.hasNext()) {
			Map.Entry me = (Map.Entry) i.next();
			String key = (String) me.getKey();
			ClauseList cl = (ClauseList) ((ClauseList) me.getValue()).clone();
			ret.put(key, cl);
		}
		return ret;
	}

	public void addToClauseLists(HashMap hm, FOPC.Node n) {

		if (n instanceof FOPC.PNode) {

			FOPC.PNode p = (FOPC.PNode) n;
			ClauseList cl = getClauseList(hm, p._sPredName, p._nArity, true);
			ArrayList al = (p._bIsNegated ? cl._alNegClauses : cl._alPosClauses);
			if (!Contains(al, n)) {
				al.add(n);
			}

		} else if (n instanceof FOPC.ConnNode
				&& ((FOPC.ConnNode) n)._nType == FOPC.ConnNode.OR) {

			Iterator i = ((FOPC.ConnNode) n)._alSubNodes.iterator();
			while (i.hasNext()) {
				FOPC.PNode p = (FOPC.PNode) i.next();
				ClauseList cl = getClauseList(hm, p._sPredName, p._nArity, true);
				ArrayList al = (p._bIsNegated ? cl._alNegClauses
						: cl._alPosClauses);
				if (!Contains(al, n)) {
					al.add(n);
				}
			}

		} else {
			System.out.println("Not in CNF!");
			System.exit(1);
		}

	}

	// WARNING: Lexical ordering inefficient... too much String generation!
	// Reorder PNodes according to a lexical ordering
	public static TreeMap _m = new TreeMap();

	public static void ReorderPNodes(FOPC.ConnNode c) {
		int k = 0;
		ArrayList l = c._alSubNodes;
		_m.clear();
		for (int i = 0; i < l.size(); i++) {
			FOPC.PNode p = (FOPC.PNode) l.get(i);
			String cur_str = p._sPredName + "_" + p._nArity + "_"
					+ (p._bIsNegated ? "T" : "F") + k;
			if (_m.containsKey(cur_str)) {
				cur_str = p._sPredName + "_" + p._nArity + "_"
						+ (p._bIsNegated ? "T" : "F") + ++k;
			}
			_m.put(cur_str, p);
		}
		l.clear();
		Iterator j = _m.entrySet().iterator();
		while (j.hasNext()) {
			Map.Entry me = (Map.Entry) j.next();
			l.add(me.getValue());
		}
	}

	// Because ArrayList contains is == rather than .equals() based
	public static boolean Contains(List l, Object o) {
		Iterator i = l.iterator();
		while (i.hasNext()) {
			if (o.equals(i.next())) {
				return true;
			}
		}
		return false;
	}

	public void removeFromClauseLists(HashMap hm, FOPC.Node n) {

		if (n instanceof FOPC.PNode) {

			FOPC.PNode p = (FOPC.PNode) n;
			ClauseList cl = getClauseList(hm, p._sPredName, p._nArity, true);
			(p._bIsNegated ? cl._alNegClauses : cl._alPosClauses).remove(n);

		} else if (n instanceof FOPC.ConnNode
				&& ((FOPC.ConnNode) n)._nType == FOPC.ConnNode.OR) {

			Iterator i = ((FOPC.ConnNode) n)._alSubNodes.iterator();
			while (i.hasNext()) {
				FOPC.PNode p = (FOPC.PNode) i.next();
				ClauseList cl = getClauseList(hm, p._sPredName, p._nArity, true);
				(p._bIsNegated ? cl._alNegClauses : cl._alPosClauses).remove(n);
			}

		} else {
			System.out.println("Not in CNF!");
			System.exit(1);
		}

	}

	public ClauseList getClauseList(HashMap hm, String predname, int arity,
			boolean create) {
		ClauseList cl = null;
		String s = predname + "_" + arity;
		if ((cl = (ClauseList) hm.get(s)) == null) {
			cl = new ClauseList();
			hm.put(s, cl);
			_hmPred2Name.put(s, predname);
			_hmPred2Arity.put(s, new Integer(arity));
		}
		return cl;
	}

	public ClauseList getClauseList(HashMap hm, String s, boolean create) {
		ClauseList cl = null;
		if ((cl = (ClauseList) hm.get(s)) == null) {
			cl = new ClauseList();
			hm.put(s, cl);
		}
		return cl;
	}

	public static class ClauseList {
		public ArrayList _alPosClauses;

		public ArrayList _alNegClauses;

		public ClauseList() {
			_alPosClauses = new ArrayList();
			_alNegClauses = new ArrayList();
		}

		public int getNumClauses() {
			return _alPosClauses.size() + _alNegClauses.size();
		}

		public Object clone() {
			ClauseList cl = new ClauseList();
			cl._alPosClauses.addAll(_alPosClauses);
			cl._alNegClauses.addAll(_alNegClauses);
			return cl;
		}

		public String toString() {
			StringBuffer sb = new StringBuffer();
			sb.append("  - POS:\n");
			Iterator i = _alPosClauses.iterator();
			while (i.hasNext()) {
				sb.append("      " + ((FOPC.Node) i.next()).toFOLString()
						+ "\n");
			}
			sb.append("  - NEG:\n");
			i = _alNegClauses.iterator();
			while (i.hasNext()) {
				sb.append("      " + ((FOPC.Node) i.next()).toFOLString()
						+ "\n");
			}
			return sb.toString();
		}
	}

	public static void ResetTimer() {
		_lTime = System.currentTimeMillis();
	}

	// Get the elapsed time since resetting the timer
	public static long GetElapsedTime() {
		return System.currentTimeMillis() - _lTime;
	}

	// /////////////////////////////////////////////////////////////////////////
	// Test Routine
	// /////////////////////////////////////////////////////////////////////////

	// Problem with free vars in clauses.
	// Look at translation time of large CNF.

	public static void main(String[] args) {

		// SetTest();
		Test1();
		Test2();
		Test3();
	}

	// Not refutable
	public static void Test1() {
		ResetTimer();
		ClauseKb kb = new ClauseKb();
		kb.addFOPCFormula("!A ?x A(?x) => B(?x)");
		kb.addFOPCFormula("!A ?x B(?x) => C(?x)");
		kb.addFOPCFormula("!A ?x B(?x) => D(?x)");
		kb.addFOPCFormula("!A ?x C(?x) ^ D(?x) => E(?x)");
		kb.addFOPCFormula("!E ?x A(?x)");
		kb.addFOPCFormula("(!E ?x E(?x))");
		// System.out.println(kb);
		kb.setOrdering();
		System.out.println("Build Kb  (" + GetElapsedTime() + " ms)");
		ResetTimer();
		System.out.println("RefuteKb = " + kb.canRefute()
				+ " [ SHOULD BE NO ] (" + GetElapsedTime() + " ms)");
	}

	// Should be refutable
	public static void Test2() {
		ResetTimer();
		ClauseKb kb = new ClauseKb();
		kb.addFOPCFormula("!A ?x A(?x) => B(?x)");
		kb.addFOPCFormula("!A ?x B(?x) => C(?x)");
		kb.addFOPCFormula("!A ?x B(?x) => D(?x)");
		kb.addFOPCFormula("!A ?x C(?x) ^ D(?x) => E(?x)");
		kb.addFOPCFormula("!E ?x A(?x)");
		kb.addFOPCFormula("~(!E ?x E(?x))");
		// System.out.println(kb);
		kb.setOrdering();
		System.out.println("Build Kb  (" + GetElapsedTime() + " ms)");
		ResetTimer();
		System.out.println("RefuteKb = " + kb.canRefute()
				+ " [ SHOULD BE YES ] (" + GetElapsedTime() + " ms)");
	}

	public static void Test3() {
		ResetTimer();
		ClauseKb kb = new ClauseKb();
		kb.addFOPCFormula("!E ?x A(?x) ^ (B(?x) | F(?x))");
		kb
				.addFOPCFormula("!E ?x A(?x) ^ (B(?x) | C(?x)) ^ (D(?x) | E(?x)) ^ (F(?x) | G(?x))");
		kb
				.addFOPCFormula("!E ?x A(?x) | (B(?x) ^ C(?x)) | (D(?x) ^ E(?x)) | (F(?x) ^ G(?x))");
		kb
				.addFOPCFormula("!A ?x A(?x) ^ (B(?x) | C(?x)) ^ (D(?x) | E(?x)) ^ (F(?x) | G(?x))");
		kb
				.addFOPCFormula("!A ?x A(?x) | (B(?x) ^ C(?x)) | (D(?x) ^ E(?x)) | (F(?x) ^ G(?x))");
		kb.addFOPCFormula("!A ?x A(?x) ^ (B(?x) | F(?x))");
		kb.addFOPCFormula("!E ?x A(?x) | (B(?x) ^ F(?x))");
		kb.addFOPCFormula("!E ?x !E ?y A(?x) ^ (B(?y) ^ F(?y))");
		kb.addFOPCFormula("!E ?x !E ?y A(?x) | (B(?y) | F(?y))");
		kb.addFOPCFormula("!A ?x !A ?y A(?x) | (B(?y) | F(?y))");
		kb.addFOPCFormula("!A ?x !A ?y A(?x) ^ (B(?y) ^ F(?y))");
		kb.addFOPCFormula("!A ?x A(?x) | (B(?x) ^ F(?x))");
		kb.addFOPCFormula("!E ?x A(?x) ^ B(?x)");
		kb.addFOPCFormula("!E ?x A(?x) | F(?x)");
		kb.addFOPCFormula("!A ?x A(?x) <=> C(?x)");
		kb.addFOPCFormula("!A ?x !E ?y A(?x,?y) ^ D(?x,?y) => C(?x,?y)");
		kb.addFOPCFormula("!A ?x (!E ?y A(?x,?y) ^ D(?x,?y)) => !E ?y C(?x)");
		kb.addFOPCFormula("!A ?x A(?x) => (C(?x) ^ D(?x))");
		kb.addFOPCFormula("!A ?x A(?x) <=> (C(?x) | F(?x))");
		kb
				.addFOPCFormula("A(?x) ^ (B(?x) | C(?x)) ^ (D(?x) | E(?x)) ^ (F(?x) | G(?x))");
		kb.addFOPCFormula("A(c1)");
		kb.addFOPCFormula("C(c1)");
		kb.addFOPCFormula("!A ?x ~D(?x)");
		// System.out.println(kb);
		kb.setOrdering();
		System.out.println("Build Kb  (" + GetElapsedTime() + " ms)");
		ResetTimer();
		System.out.println("RefuteKb = " + kb.canRefute()
				+ " [ SHOULD BE YES ] (" + GetElapsedTime() + " ms)");
	}

	// Shows that duplicates in a set of sets are removed
	public static void SetTest() {
		HashSet s1 = new HashSet();
		HashSet s2 = new HashSet();
		HashSet s3 = new HashSet();
		HashSet s4 = new HashSet();
		s2.add("A");
		s2.add("B");
		s3.add("A");
		s3.add("B");
		s4.add("A");
		s4.add("B");
		s4.add("C");
		s1.add(s2);
		s1.add(s3);
		s1.add(s4);
		System.out.println(s1);
	}
}
