package logic;
import java.io.*;
import java.util.*;

// public class PropKbCNF extends Kb {
public class PropKbCNF {
	public static final String SAT_EXECUTABLE = "minisat114.exe";
	
	// Kb status constants
	public static final int INDETERMINATE = 0;
	public static final int TAUTOLOGY = 1;
	public static final int INCONSISTENT = 2;

	// Data members for formula storage and var->id mapping
	public int _nLiteralIDCount; // id counter for this kb
	public boolean _bUseExternalReasoner;
	public ArrayList _alLiteralList; // for id, returns PropLiteral
	public ArrayList _alAssignment; // assignment for given var id
	public HashMap _hmLiteralToID; // maps literal string -> id
	public HashSet<HashSet<PropFormula.Term>> _cnfCurrentKb; // could add undo's here later :)

	// Constructor (no params)
	public PropKbCNF() {
		this(true);
	}
	
	public PropKbCNF(boolean use_external_reasoner) {
		_bUseExternalReasoner = use_external_reasoner;
		_nLiteralIDCount = 1;
		_alLiteralList = new ArrayList();
		_alLiteralList.add(new Exception("Should not access first element"));
		_alAssignment = new ArrayList();
		_hmLiteralToID = new HashMap();
		_cnfCurrentKb = new HashSet<HashSet<PropFormula.Term>>();
	}

	////////////////////////////////////////////////////////////////////////////
	// Primitive Interface Routines
	////////////////////////////////////////////////////////////////////////////

	// Get a PropLiteral given a string... will check
	// cache in case already created... cannot be static
	// because relies on local PropManager.
	public PropLiteral getLiteral(String name) {

		// Does literal already exist?
		Integer iid = (Integer) _hmLiteralToID.get(name);

		if (iid == null) {
			// Create a new literal and return
			int id = _nLiteralIDCount++;
			PropLiteral p = new PropLiteral(name, id);
			_alLiteralList.add(p);
			_alAssignment.add(null);
			_hmLiteralToID.put(name, new Integer(id));
			return p;
		} else {
			// Get current literal and return
			return (PropLiteral) _alLiteralList.get(iid.intValue());
		}
	}

	public PropLiteral getLiteral(int id) {
		if (id < _alLiteralList.size()) {
			return (PropLiteral) _alLiteralList.get(id);
		} else {
			return null;
		}
	}

	public PropLiteral getNewLiteral() {
		String n = "<" + _nLiteralIDCount + ">";
		int id = _nLiteralIDCount++;
		PropLiteral p = new PropLiteral(n, id);
		_alLiteralList.add(p);
		_hmLiteralToID.put(n, new Integer(id));
		return p;
	}

	// Builds a right recursive conjunction of terms,
	// subterms must be empty or only have objects
	// of type PropFormula.Term.
	public static PropFormula.Term getConjTerm(List subterms) {
		if (subterms.isEmpty()) {
			return new PropConstant(true);
		} else {
			Iterator i = subterms.iterator();
			PropFormula.Term cur = (PropFormula.Term) i.next();
			while (i.hasNext()) {
				cur = new PropBinConn(cur, (PropFormula.Term) i.next(),
						PropFormula.BinConn.AND);
			}
			return cur;
		}
	}

	// Builds a right recursive disjunction of terms,
	// subterms must be empty or only have objects
	// of type PropFormula.Term.
	public static PropFormula.Term getDisjTerm(List subterms) {
		if (subterms.isEmpty()) {
			return new PropConstant(false);
		} else {
			Iterator i = subterms.iterator();
			PropFormula.Term cur = (PropFormula.Term) i.next();
			while (i.hasNext()) {
				cur = new PropBinConn(cur, (PropFormula.Term) i.next(),
						PropFormula.BinConn.OR);
			}
			return cur;
		}
	}

	// Builds an implication from a list... empty list is true
	// (correct?). (a b c d) is considered to be (a^b^c => d).
	public static PropFormula.Term getImpliesTerm(List subterms) {
		if (subterms.isEmpty()) {
			return new PropConstant(true);
		} else {
			PropFormula.Term implicant = (PropFormula.Term) subterms
					.remove(subterms.size() - 1);
			PropFormula.Term LHS = getConjTerm(subterms);
			return new PropBinConn(LHS, implicant, PropFormula.BinConn.IMPLIES);
		}
	}

	// Builds an equivalence relation for exactly two terms (multiple
	// terms are not allowed here).
	public static PropFormula.Term getEquivTerm(List subterms) {
		if (subterms.size() != 2) {
			System.out
					.println("Can only use <=> for two terms, use paren grouping for multiple terms");
			System.exit(1);
			return null;
		} else {
			Iterator i = subterms.iterator();
			PropFormula.Term lhs = (PropFormula.Term) i.next();
			PropFormula.Term rhs = (PropFormula.Term) i.next();
			return new PropBinConn(lhs, rhs, PropFormula.BinConn.EQUIV);
		}
	}

	////////////////////////////////////////////////////////////////////////////
	// ADD to Formula Conversion Routine
	////////////////////////////////////////////////////////////////////////////

	// Internal class for representing boolean partition
	public static class PropBPart {
		public PropFormula.Term _term;
		public boolean _bVal;

		public PropBPart(PropFormula.Term pt, boolean val) {
			_term = pt;
			_bVal = val;
		}
	}

	// Internal class for representing double partition
	public static class PropDPart {
		public PropFormula.Term _term;
		public double _dLower;
		public double _dUpper;
		public String _sLabel;

		public PropDPart(PropFormula.Term pt, double lower, double upper) {
			this(pt, lower, upper, null);
		}

		public PropDPart(PropFormula.Term pt, double lower, double upper,
				String label) {
			_term = pt;
			_dLower = lower;
			_dUpper = upper;
			_sLabel = label;
		}
	}

	// Simplify since likely used for reading
	public HashSet<HashSet<PropFormula.Term>> getKb() {
		return _cnfCurrentKb;
	}
	
	// Converts a PropFormula to negation normal form (NNF)
	public static PropFormula.Term ConvertNNF(PropFormula.Term form,
			boolean invert) {

		if (form instanceof PropBinConn) {

			PropBinConn pb = (PropBinConn) form;
			switch (pb.getType()) {

			case PropBinConn.OR: {

				return new PropBinConn(ConvertNNF(pb.getLTerm(), invert),
						ConvertNNF(pb.getRTerm(), invert),
						invert ? PropBinConn.AND : PropBinConn.OR);
			}

			case PropBinConn.AND: {

				return new PropBinConn(ConvertNNF(pb.getLTerm(), invert),
						ConvertNNF(pb.getRTerm(), invert),
						invert ? PropBinConn.OR : PropBinConn.AND);
			}

			default: {
				System.out.println("ConvertNNF: Illegal binary connective " + 
						form + " : " + ((PropBinConn)form).getType());
				new Exception().printStackTrace();
				System.exit(1);
				return null; // Never reached!
			}

			}

		} else if (form instanceof PropUnConn) {

			PropUnConn pu = (PropUnConn) form;
			if (pu.getType() != PropUnConn.NEG) {
				System.out.println("Illegal unary prop connective");
				System.exit(1);
			}

			return ConvertNNF(pu.getTerm(), !invert);

		} else if (form instanceof PropLiteral) {

			PropLiteral pl = (PropLiteral) form;
			if (invert) {
				return new PropUnConn(pl, PropUnConn.NEG);
			} else {
				return pl;
			}

		} else {

			PropConstant pc = (PropConstant) form;
			if (invert) {
				return new PropConstant(!pc.getTruthValue());
			} else {
				return pc;
			}

		}

	}

	// Converts a propositional formula to DNF
	public static HashSet<HashSet<PropFormula.Term>> ConvertCNF(PropFormula.Term form) {
		PropFormula.Term imp_form = RemoveEquiv(form);
		PropFormula.Term and_or_form = RemoveImplies(imp_form);
		PropFormula.Term nnf_form = ConvertNNF(and_or_form, false);
		if (imp_form == null || and_or_form == null || nnf_form == null)
			System.out.println("ERROR: null intermediate value");
		HashSet<HashSet<PropFormula.Term>> result = DistOrOverAnd(nnf_form);
		if (result == null) {
			System.out.println("ERROR: DistOrOverAnd failed");
		}
		
		// Filter tautologies
		HashSet<HashSet<PropFormula.Term>> filter_result = new HashSet<HashSet<PropFormula.Term>>();
		for (HashSet<PropFormula.Term> clause : result)
			if (!tautology(clause))
				filter_result.add(clause);
		return result;
	}
	
	public static boolean tautology(HashSet<PropFormula.Term> clause) {
		for (PropFormula.Term t : clause) {
			// Assumes PropUnConn is negation... should always be case
			if (t instanceof PropUnConn) { 
				PropUnConn un = (PropUnConn)t;
				if (clause.contains(un._term))
					return true;
			} else {
				PropUnConn un = new PropUnConn(t, PropUnConn.NEG);
				if (clause.contains(un))
					return true;
			}
		}
		return false;
	}
	
	// Remove equivlances
	public static PropFormula.Term RemoveEquiv(PropFormula.Term form) {

		if (form instanceof PropBinConn && 
			((PropBinConn)form).getType() == PropBinConn.EQUIV) {

			PropBinConn pb = (PropBinConn) form;
			PropFormula.Term lterm_cnf = RemoveEquiv(pb.getLTerm());
			PropFormula.Term rterm_cnf = RemoveEquiv(pb.getRTerm());

			return new PropBinConn(
				new PropBinConn(lterm_cnf, rterm_cnf, PropBinConn.IMPLIES),
				new PropBinConn(rterm_cnf, lterm_cnf, PropBinConn.IMPLIES), 
				PropBinConn.AND);
		} else if (form instanceof PropBinConn) {
			
			PropBinConn pb = (PropBinConn) form;
			pb._termL = RemoveEquiv(pb.getLTerm());
			pb._termR = RemoveEquiv(pb.getRTerm());
			return pb;

		} else if (form instanceof PropUnConn) {
			PropUnConn un = (PropUnConn) form;
			un._term = RemoveEquiv(un._term);
			return un;
		} else		
			return form;
	}

	// Remove implications
	public static PropFormula.Term RemoveImplies(PropFormula.Term form) {

		if (form instanceof PropBinConn && 
			((PropBinConn)form).getType() == PropBinConn.IMPLIES) {

			PropBinConn pb = (PropBinConn) form;
			PropFormula.Term lterm_cnf = RemoveImplies(pb.getLTerm());
			PropFormula.Term rterm_cnf = RemoveImplies(pb.getRTerm());

			return new PropBinConn(new PropUnConn(lterm_cnf, PropFormula.UnConn.NEG), 
					rterm_cnf, PropBinConn.OR);
			
		} else if (form instanceof PropBinConn) {
			
			PropBinConn pb = (PropBinConn) form;
			pb._termL = RemoveImplies(pb.getLTerm());
			pb._termR = RemoveImplies(pb.getRTerm());
			return pb;

		} else if (form instanceof PropUnConn) {
			
			PropUnConn un = (PropUnConn) form;
			un._term = RemoveImplies(un._term);
			return un;
			
		} else			
			return form;
	}

	// Result is a set of clauses (themselves sets of literals)
	public static HashSet<HashSet<PropFormula.Term>> DistOrOverAnd(PropFormula.Term form) {

		if (form instanceof PropBinConn) {

			PropBinConn pb = (PropBinConn) form;
			HashSet<HashSet<PropFormula.Term>> lterm_cnf = DistOrOverAnd(pb.getLTerm());
			HashSet<HashSet<PropFormula.Term>> rterm_cnf = DistOrOverAnd(pb.getRTerm());

			HashSet<HashSet<PropFormula.Term>> ret = new HashSet<HashSet<PropFormula.Term>>();
			
			switch (pb.getType()) {

			case PropBinConn.AND: {
				lterm_cnf.addAll(rterm_cnf);
				return lterm_cnf;
			}

			case PropBinConn.OR: {

				for (HashSet<PropFormula.Term> l : lterm_cnf) {
					for (HashSet<PropFormula.Term> r : rterm_cnf) {
						HashSet<PropFormula.Term> new_clause = new HashSet<PropFormula.Term>();
						new_clause.addAll(l);
						new_clause.addAll(r);
						ret.add(new_clause);
					}
				}
				return ret;
			}
			
			default: {
				System.out.println("ERROR: Illegal binary connective: " + form);
				System.exit(1);
				return null;
			}
			}

		} else {

			// Any unary, literal, or constant node must be at the bottom so
			// base case for DNF... return!
			HashSet<PropFormula.Term> clause = new HashSet<PropFormula.Term>();
			
			// Should be in NNF so only need to remove double negatives at leaves
			clause.add(removeDoubleNeg(form));
			HashSet<HashSet<PropFormula.Term>> ret = new HashSet<HashSet<PropFormula.Term>>();
			ret.add(clause);
			return ret;
		}

	}

	public static PropFormula.Term removeDoubleNeg(PropFormula.Term form) {
		if (form instanceof PropUnConn && 
				((PropUnConn)form)._nType == PropUnConn.NEG) {
			PropUnConn un = (PropUnConn)form;
			if (un._term instanceof PropUnConn && 
					((PropUnConn)un._term)._nType == PropUnConn.NEG) {
				return ((PropUnConn)un._term)._term;
			} 
		}
		return form;
	}
	
	////////////////////////////////////////////////////////////////////////////
	// Main External Interface Routines
	////////////////////////////////////////////////////////////////////////////

	// Adds formula given by a string to a kb
	public HashSet<HashSet<PropFormula.Term>> getFormula(String s) {
		ParseStruct ps = parseFormula(s, 0 /* start pos */);
		return ConvertCNF(ps._propTerm);
	}
	
	public void addFormula(String s) {
		ParseStruct ps = parseFormula(s, 0 /* start pos */);
		addFormula(ps._propTerm);
	}

	// Conjoins (ANDs) current kb with formula... beauty of
	// ADD.GetADD() is that so long as one can guarantee
	// literal id's are consistent, it will produce the
	// proper id. We guarantee consistency by using this
	// kb to keep track of literal->id mappings. Should
	// add undo here. :)
	public void addFormula(PropFormula.Term formula) {
		//System.out.println("Adding: " + formula + " as CNF\n" + ConvertCNF(formula));
		_cnfCurrentKb.addAll(ConvertCNF(formula));
	}

	public String toString() {
		StringBuffer sb = new StringBuffer("ID Map:    ");
		Iterator i = _alLiteralList.iterator();
		while (i.hasNext()) {
			Object o = i.next();
			if (!(o instanceof PropLiteral)) 
				continue;
			PropLiteral l = (PropLiteral)o;
			sb.append(l._sName + "->" + l._nID + " ");
		}
		sb.append("\n" + _cnfCurrentKb);
		return sb.toString();
	}

	////////////////////////////////////////////////////////////////////////////
	// Internal Formula Representation - Implements PropFormula
	////////////////////////////////////////////////////////////////////////////

	public static class PropBinConn extends PropFormula.BinConn {

		public PropFormula.Term _termL;
		public PropFormula.Term _termR;
		public int _nType;

		public PropBinConn(PropFormula.Term l, PropFormula.Term r, int type) {
			_termL = l;
			_termR = r;
			_nType = type;
		}

		public PropFormula.Term getLTerm() {
			return _termL;
		}

		public PropFormula.Term getRTerm() {
			return _termR;
		}

		public int getType() {
			return _nType;
		}

		public String toString() {
			String conn = null;
			switch (_nType) {
			case PropBinConn.AND: conn = " ^ "; break;
			case PropBinConn.OR:  conn = " | "; break; 
			case PropBinConn.IMPLIES: conn = " => "; break;
			case PropBinConn.EQUIV:   conn = " <=> "; break;
			default: conn = " [INVALID] "; break;
			}
			return "( " + _termL.toString() + conn + _termR.toString() + " )";
		}

		// Perform structural comparison
		public boolean equals(Object o) {

			if (o instanceof PropBinConn) {

				// Avoiding checking cross terms because this would lead to
				// exponential
				// recursions
				PropBinConn b = (PropBinConn) o;
				return (_nType == b._nType)
						&& (_termL.equals(b._termL) && _termR.equals(b._termR));

			} else {
				return false;
			}

		}

	}

	public static class PropUnConn extends PropFormula.UnConn {

		public PropFormula.Term _term;
		public int _nType;

		public PropUnConn(PropFormula.Term t, int type) {
			_term = t;
			_nType = type;
		}

		public PropFormula.Term getTerm() {
			return _term;
		}

		public int getType() {
			return _nType;
		}

		public String toString() {
			return (_nType == NEG ? "~" : "?") + _term;
		}

		// Perform structural comparison
		public boolean equals(Object o) {

			if (o instanceof PropUnConn) {

				PropUnConn u = (PropUnConn) o;
				return (_nType == u._nType) && _term.equals(u._term);

			} else {
				return false;
			}

		}

	}

	public static class PropLiteral extends PropFormula.Prop {

		public String _sName;
		public int _nID;

		// Create a new literal
		public PropLiteral(String name, int id) {
			_sName = name;
			_nID = id;
		}

		// Unique id for a literal
		public int getID() {
			return _nID;
		}

		public String toString() {
			if (_sName != null) {
				return _sName + ":" + _nID;
			} else {
				return "v" + _nID;
			}
		}

		// Perform structural comparison
		public boolean equals(Object o) {

			if (o instanceof PropLiteral) {

				PropLiteral l = (PropLiteral) o;
				return _nID == l._nID;

			} else {
				return false;
			}

		}

	}

	public static class PropConstant extends PropFormula.TruthConstant {

		public boolean _bVal;

		public PropConstant(boolean val) {
			_bVal = val;
		}

		public boolean getTruthValue() {
			return _bVal;
		}

		public String toString() {
			return "" + _bVal; // Ugly, but works :)
		}

		// Perform structural comparison
		public boolean equals(Object o) {

			if (o instanceof PropConstant) {

				PropConstant c = (PropConstant) o;
				return _bVal == c._bVal;

			} else {
				return false;
			}

		}
	}

	////////////////////////////////////////////////////////////////////////////
	// Parsing Subroutine
	////////////////////////////////////////////////////////////////////////////

	// Parse a formula string and return the Term tree (create all
	// necessary literals in current kb). This is a simple parser
	// that simply recurses for every '(' encountered and pops for
	// every ')' encountered. Within any recursion level, either '^',
	// '|', '<=>' or '=>' must be used exclusively. So "~a ^ b | c"
	// is illegal, but "(~a ^ b) | c" is legal. Note: T and F are
	// interpreted as true and false *constants*. Negations must be
	// followed by a char or opening paren. This allows some illegal
	// syntax but it works for the most part. :)
	public static class ParseStruct {
		public int _nFinalPos;
		public PropFormula.Term _propTerm;
	}

	public ParseStruct parseFormula(String s, int start_pos) {

		int pos = start_pos;
		int pos_max = s.length();
		boolean conj = false;
		boolean disj = false;
		boolean neg = false;
		boolean implies = false;
		boolean equiv = false;
		ArrayList terms = new ArrayList();
		String cur_lit = null;

		// Read string, parsing off literals and checking
		// for type. If '(' reached then recurse and
		// continue from _nFinalPos. If ')' or end of
		// string reached, return pos and formula.
		for (; pos < pos_max; pos++) {

			char c = s.charAt(pos);

			// System.out.println("Checking '" + c + "'");

			switch (c) {

			case '(': {
				ParseStruct ps = parseFormula(s, pos + 1);
				pos = ps._nFinalPos;
				if (neg) {
					terms.add(new PropUnConn(ps._propTerm,
							PropFormula.UnConn.NEG));
				} else {
					terms.add(ps._propTerm);
				}
				neg = false;
			}
				break;

			case ')': {
				// First check to close a literal - ugly
				if (cur_lit != null) {
					if (neg) {
						terms.add(new PropUnConn(getLiteral(cur_lit),
								PropFormula.UnConn.NEG));
					} else {
						terms.add(getLiteral(cur_lit));
					}
					cur_lit = null;
					neg = false;
				}

				// Now return the correct structure - this also occurs below!!!
				// Ugly code... need to update.
				ParseStruct ps = new ParseStruct();
				ps._nFinalPos = pos;
				if (conj) {
					ps._propTerm = getConjTerm(terms);
				} else if (disj) {
					ps._propTerm = getDisjTerm(terms);
				} else if (implies) {
					ps._propTerm = getImpliesTerm(terms);
				} else if (equiv) {
					ps._propTerm = getEquivTerm(terms);
				} else if (terms.size() == 1) {
					ps._propTerm = (PropFormula.Term) terms.get(0);
				} else {
					System.out.println("Formula error: malformed subformula");
					System.exit(1);
				}
				return ps;
			}

			case 'T': {
				if (cur_lit != null) {
					System.out.println("Formula error: T occurs in prop lit");
					System.exit(1);
				}
				if (neg) {
					terms.add(new PropConstant(false));
				} else {
					terms.add(new PropConstant(true));
				}
				neg = false;
			}
				break;

			case 'F': {
				if (cur_lit != null) {
					System.out.println("Formula error: F occurs in prop lit");
					System.exit(1);
				}
				if (neg) {
					terms.add(new PropConstant(true));
				} else {
					terms.add(new PropConstant(false));
				}
				neg = false;

			}
				break;

			case '~': {
				neg = !neg;
			}
				break;

			// Because of this style of parser, there are many incorrect
			// ways to specify => that will still parse correctly, need
			// to be careful!
			case '=':
			case '<':
			case '^':
			case '|':
			case ' ':
			case '\t':
			case '\r':
			case '\n': {

				// We assume that only one of {^,|,=>} can occur per
				// level so we set the implies flag
				if (c == '<') {
					if (conj || disj || implies) {
						System.out
								.println("Formula error: ^,|,=>,<=> at same level");
						System.exit(1);
					}
					if (s.charAt(++pos) != '=') {
						System.out
								.println("Formula error: < must be followed by =");
						System.exit(1);
					}
					if (s.charAt(++pos) != '>') {
						System.out
								.println("Formula error: <= must be followed by >");
						System.exit(1);
					}
					equiv = true;
				} else if (c == '=') {
					if (conj || disj || equiv) {
						System.out
								.println("Formula error: ^,|,=>,<=> at same level");
						System.exit(1);
					}
					if (s.charAt(++pos) != '>') {
						System.out
								.println("Formula error: = must be followed by >");
						System.exit(1);
					}
					implies = true;
				} else if (c == '^') {
					if (implies || disj || equiv) {
						System.out
								.println("Formula error: ^,|,=>,<=> at same level");
						System.exit(1);
					}
					conj = true;
				} else if (c == '|') {
					if (implies || conj || equiv) {
						System.out
								.println("Formula error: ^,|,=>,<=> at same level");
						System.exit(1);
					}
					disj = true;
				}

				// Whitespace so break cur_lit
				if (cur_lit != null) {
					if (neg) {
						terms.add(new PropUnConn(getLiteral(cur_lit),
								PropFormula.UnConn.NEG));
					} else {
						terms.add(getLiteral(cur_lit));
					}
					cur_lit = null;
					neg = false;
				} else if (neg) {
					System.out
							.println("Formula error: ~ followed by whitespace?");
					System.exit(1);
				}

			}
				break;

			default: {
				// Interpret as a character
				if (cur_lit == null) {
					cur_lit = String.valueOf(c);
				} else {
					cur_lit = cur_lit + c;
				}
			}

			}

		}

		// First see if we need to close any literals
		if (cur_lit != null) {
			if (neg) {
				terms.add(new PropUnConn(getLiteral(cur_lit),
						PropFormula.UnConn.NEG));
			} else {
				terms.add(getLiteral(cur_lit));
			}
			cur_lit = null;
			neg = false;
		}

		// Now return the correct structure
		ParseStruct ps = new ParseStruct();
		ps._nFinalPos = pos;
		if (conj) {
			ps._propTerm = getConjTerm(terms);
		} else if (disj) {
			ps._propTerm = getDisjTerm(terms);
		} else if (implies) {
			ps._propTerm = getImpliesTerm(terms);
		} else if (equiv) {
			ps._propTerm = getEquivTerm(terms);
		} else if (terms.size() == 1) {
			ps._propTerm = (PropFormula.Term) terms.get(0);
		} else {
			System.out.println("Formula error: Malformed formula");
			System.exit(1);
		}
		return ps;

	}

	public boolean querySATSolver(String query) {
		return queryInternalSATSolver(query);
	}
	
	public boolean queryInternalSATSolver(String query) {
		ByteArrayOutputStream bs = new ByteArrayOutputStream();
		exportDIMACSQuery(new PrintStream(bs), query);
		BufferedReader br = new BufferedReader(new InputStreamReader(
				new ByteArrayInputStream(bs.toByteArray())));
		
		SimpleDPLL dpll = new SimpleDPLL();

		try {
			dpll.readDIMACSFile(br);
		} catch (Exception e) {
			System.out.println("Error reading from DIMACS input:\n" + bs.toString());
			System.exit(1); // Fail ungracefully
		}
		return dpll.unsat();
	}
	
	public void exportDIMACSQuery(String filename, String query) {
		try {
			PrintStream os = new PrintStream(new FileOutputStream(filename));
			exportDIMACSQuery(os, query);
			os.close();
		} catch (Exception e) {
			System.out.println("ERROR EXPORTING '" + filename + "': " + e);
			e.printStackTrace();
		}
	}

	public void exportDIMACSQuery(PrintStream os, String query) {
		
		HashSet<HashSet<PropFormula.Term>> query_clauses = getFormula("~(" + query + ")");
		query_clauses.addAll(_cnfCurrentKb);
		
		try {
			os.println("p cnf " + (_nLiteralIDCount - 1) + " " + query_clauses.size());
			
			Iterator i = _alLiteralList.iterator();
			while (i.hasNext()) {
				Object o = i.next();
				if (!(o instanceof PropLiteral)) 
					continue;
				PropLiteral l = (PropLiteral)o;
				os.println("c " + l._sName + " -> #" + l._nID + " ");
			}
			for (HashSet<PropFormula.Term> clause : query_clauses) {
				os.println(getDIMACSClause(clause));
			}
		} catch (Exception e) {
			System.out.println("ERROR EXPORTING: " + e);
			e.printStackTrace();
		}
	}
	
	public String getDIMACSClause(HashSet<PropFormula.Term> clause) {
		StringBuilder sb = new StringBuilder();
		for (PropFormula.Term t : clause) {
			PropLiteral l = null;
			if (t instanceof PropUnConn) {
				l = (PropLiteral)((PropUnConn)t)._term;
				sb.append("-" + l._nID + " ");
			} else if (t instanceof PropLiteral) {
				l = (PropLiteral)t;
				sb.append(l._nID + " ");
			} else 
				return "MALFORMED CLAUSE: " + clause;
		}
		sb.append("0");
		return sb.toString();
	}
}
