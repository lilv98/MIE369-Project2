package logic;
import utils.*;
import java.io.*;
import java.util.ArrayList;

public class PropAskTell {
	/* Static constants */
	public final static int MAX_INPUT = 4096;
	public final static int INDENT = 3;
	public final static boolean USE_EXTERNAL_SAT_SOLVER = false;

	/* Command shell flags */
	public boolean SHOW_CNF_ON_ADD = false;

	/* Encapsulated Objects */
	public CommandInterface _ci;
	public InputStream _is;
	public PrintStream _os;
	public PropKbCNF _kb;
	public ArrayList<String> _axioms;
	public long _lStartTime;

	/* Class-defined commands */
	public int QUIT;
	public int COMMENT;
	public int NEW_KB;
	public int EXPORT_DIMACS;
	public int PROP_TELL;
	public int PROP_ASK;
	public int SHOW_KB;
	public int SHOW_CNF;
	public int TIMER;

	/**
	 * Initializes the shell interface and invokes it
	 **/
	public static void main(String args[]) {
		try {
			InputStream in;
			if (args.length >= 1)
				in = new FileInputStream(args[0]);
			else
				in = System.in;
			PropAskTell shell = new PropAskTell(in, System.out);
			shell.run();
		} catch (FileNotFoundException e) {
			System.out.println("File IO Error while reading " + args[0] + ", exiting...");
			System.exit(1);
		}
	}

	/**
	 * Constructor
	 * @param is: InputStream to read input from
	 * @param os: OutputStream to write output to
	 **/
	public PropAskTell(InputStream is, PrintStream os) {
		_is = is;
		_os = os;
		_ci = new CommandInterface(_is, _os);
		_axioms = new ArrayList<String>();

		// Initialize a set of commands
		TIMER = _ci.command.addCommand("timer",
				" {start|stop}                  - start or stop timer");
		QUIT = _ci.command.addCommand("quit",
				"                                - quit application");
		COMMENT = _ci.command.addCommand("//",
				"                                  - comment\n");
		NEW_KB = _ci.command.addCommand("new-kb",
				"                              - make a new knowledge base of the given type");
		EXPORT_DIMACS = _ci.command.addCommand("export-dimacs",
				" <filename> <query>    - export the current KB and a possible negated query in DIMACS format");
		SHOW_KB = _ci.command.addCommand("show-kb",
				" [ext]                       - display current axioms in kb");
		SHOW_CNF = _ci.command.addCommand("show-cnf",
				" {true,false}               - display current axioms in kb");
		PROP_TELL = _ci.command
				.addCommand("tell",
						" <string>                       - tell a propositional statement to the kb");
		PROP_ASK = _ci.command
				.addCommand("ask",
						" <string>                        - query truthhood of propositional string in kb");

		// Initialize time
		_lStartTime = 0L;

		// Initialize the domain
		_kb = new PropKbCNF(USE_EXTERNAL_SAT_SOLVER);
		_os.println("\nCreated new " + (USE_EXTERNAL_SAT_SOLVER ? "external inference" : "internal inference") + " kb.");
	}

	/**
	 * Main command line handler
	 **/
	public void run() {

		while (_ci.command.type != QUIT) {

			try {
				_ci.getCommand();
			} catch (IOException e) {
				_os.println("IO Error: " + e);
				System.exit(1);
			}

			/***********************************************************
			 * Command: Quit
			 ***********************************************************/
			if (_ci.command.type == QUIT) {
				_os.println("\nExiting LShell\n");
			}

			/***********************************************************
			 * Command: Handle timer commands
			 ***********************************************************/
			else if (_ci.command.type == TIMER) {

				if (_ci.command.numParams() != 1) {
					_os.println("\nNeed to specify either 'start' or 'stop'.");
				} else {
					String com = _ci.command.getParam(0);
					if (com.equalsIgnoreCase("start")) {
						_lStartTime = System.currentTimeMillis();
					} else if (com.equalsIgnoreCase("stop")) {
						_os.println("\nElapsed time: "
								+ (System.currentTimeMillis() - _lStartTime)
								+ " ms");
					} else {
						_os.println("\nUnrecognized timer command");
					}
				}
			}

			/***********************************************************
			 * Command: Comment '//'
			 ***********************************************************/
			if (_ci.command.type == COMMENT) {
				; // Do nothing
			}

			/***********************************************************
			 * Command: New KB
			 ***********************************************************/
			else if (_ci.command.type == NEW_KB) {

				boolean external_sat = USE_EXTERNAL_SAT_SOLVER;
				
				if (_ci.command.numParams() >= 1) {
					String use_external = _ci.command.getParam(0);
					external_sat = use_external.indexOf("ext") >= 0;
				}
				
				// Obtain the domain title (if provided)
				_axioms.clear();
				_kb = new PropKbCNF(external_sat);

				// Print results
				_os.println("\nCreated new " + (external_sat ? "external inference" : "internal inference") + " Prop KB.");
			}

			/***********************************************************
			 * Command: Export DIMACS
			 ***********************************************************/
			else if (_ci.command.type == EXPORT_DIMACS) {
		
				if (_ci.command.numParams() >= 2) {
					String filename = _ci.command.getParam(0);
					String query    = _ci.command.getParam(1);

					_kb.exportDIMACSQuery(filename, query);
					_os.println("\nExported DIMACS file to '" + filename + "' with ~query: " + query);
				
				} else
					_os.println("\nMust include filename and query as arguments.");
				
			}

			/***********************************************************
			 * Command: Show KB
			 ***********************************************************/
			else if (_ci.command.type == SHOW_KB) {

				// Show all axioms added so far
				_os.println("\nPropositional Logic KB Axioms:");
				for (String axiom : _axioms) {
					_os.println("* " + axiom);
				}
			}
			
			/***********************************************************
			 * Command: Show CNF
			 ***********************************************************/
			else if (_ci.command.type == SHOW_CNF) {
			
				if (_ci.command.numParams() >= 1) {
					String show_cnf_param = _ci.command.getParam(0);
					SHOW_CNF_ON_ADD = show_cnf_param.indexOf("true") >= 0;
				}
				
				_os.println("\nShow CNF set to " + SHOW_CNF_ON_ADD);
			}

			/***********************************************************
			 * Command: Tell
			 ***********************************************************/
			else if (_ci.command.type == PROP_TELL) {

				if (_ci.command.numParams() != 1) {
					_os.println("\nMust specify a single FOPC string as param.");
				} else {

					// Process the command
					try {
						String query = _ci.command.getParam(0);
						//String formula = FOPC.parse(query).toKIFString();
						//_os.println("Adding KIF formula '" + formula + "' to " + _kb);
						_kb.addFormula(query);
						_axioms.add(query);
						if (SHOW_CNF_ON_ADD)
							_os.println("\nCNF: " + _kb.getFormula(query));
					} catch (Exception e) {
						// Just continue
					}
				}
			}

			/***********************************************************
			 * Command: Ask
			 ***********************************************************/
			else if (_ci.command.type == PROP_ASK) {

				if (_ci.command.numParams() != 1) {
					_os.println("\nMust specify a single FOPC string as param.");
				} else {

					// Process the command
					try {
						String query = _ci.command.getParam(0);
						_os.println("\nResult: " + (_kb.querySATSolver(query) ? "entailed" : "not entailed"));
					} catch (Exception e) {
						System.err.println(e);
					}
				}
			}

		}
	}

}
