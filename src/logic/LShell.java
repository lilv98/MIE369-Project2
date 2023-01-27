//////////////////////////////////////////////////////////////////////
//
// File:     LShell.java
// Project:  MIE457F Data Mining System
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     9/1/2003
// Requires: comshell package
//
// Description:
//
//   A command line interface to the logic.kb.fol package.
//
//////////////////////////////////////////////////////////////////////

// Package definition
package logic;

// Packages to import
import comshell.*;
import java.io.*;

import logic.kb.Kb;
// import logic.kb.fol.*;

/**
 * Text shell interface for a logical inference system
 * 
 * @version 1.0
 * @author Scott Sanner
 * @language Java (JDK 1.3)
 **/
public class LShell {
	/* Static constants */
	public final static int MAX_INPUT = 4096;
	public final static String DEFAULT_PREFS_FILE = "prefs.txt";
	public final static int INDENT = 3;

	/* Encapsulated Objects */
	public CommandInterface _ci;
	public InputStream _is;
	public PrintStream _os;
	public Kb _kb;
	public long _lStartTime;

	/* Class-defined commands */
	public int QUIT;
	public int COMMENT;
	public int NEW_KB;
	public int FOL_TELL;
	public int FOL_ASK;
	public int FOL_ASKB;
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

			LShell shell = new LShell(in, System.out);
			shell.run();

		} catch (FileNotFoundException e) {
			System.out.println("File IO Error while reading " + args[0]
					+ ", exiting...");
			System.exit(1);
		}

	}

	/**
	 * Empty constructor - uses System input/output stream and default
	 * preferences file.
	 **/
	public LShell() {
		this(System.in, System.out, DEFAULT_PREFS_FILE);
	}

	/**
	 * Constructor - uses default preferences file.
	 * 
	 * @param is
	 *            InputStream to read input from
	 * @param os
	 *            OutputStream to write output to
	 **/
	public LShell(InputStream is, PrintStream os) {
		this(is, os, DEFAULT_PREFS_FILE);
	}

	/**
	 * Constructor
	 * 
	 * @param is
	 *            InputStream to read input from
	 * @param os
	 *            OutputStream to write output to
	 * @param prefs_file
	 *            File to load default environmental variable
	 *            bindings/preferences from
	 **/
	public LShell(InputStream is, PrintStream os, String prefs_file) {
		_is = is;
		_os = os;
		_ci = new CommandInterface(_is, _os);

		// Initialize a set of commands
		TIMER = _ci.command.addCommand("timer",
				" {start|stop}                  - start or stop timer");
		QUIT = _ci.command.addCommand("quit",
				"                                - quit application");
		COMMENT = _ci.command.addCommand("//",
				"                                  - comment\n");
		NEW_KB = _ci.command.addCommand("new-kb",
				" [ext-fol] - make a new knowledge base of the given type");
		FOL_TELL = _ci.command
				.addCommand("tell",
						" <string>                       - tell a FOPC string to the kb");
		FOL_ASK = _ci.command
				.addCommand("ask",
						" <string>                        - query truthhood of FOPC string in kb");
		FOL_ASKB = _ci.command
				.addCommand("askb",
						" <string>                       - retrieve bindings for FOPC string from kb");

		// Initialize environmental variable bindings from preferences file
		_ci.initEnvVarsFromFile(prefs_file);

		// Initialize time
		_lStartTime = 0L;

		// Initialize the domain
		_kb = new ClauseKb();
		_os.println("\nCreated new default kb '" + _kb + "'...");
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

				// Obtain the domain title (if provided)
				if (_ci.command.numParams() >= 1) {
					String param = _ci.command.getParam(0);
					if (param.equalsIgnoreCase("ext-fol"))
						_kb = new ClauseKb();
					//else if (param.equalsIgnoreCase("java-prop"))
					//	_kb = new PropKbCNF(false /*use external SAT solver*/);
					//else if (param.equalsIgnoreCase("ext-prop"))
					//	_kb = new PropKbCNF(true /*use external SAT solver*/);
					//else if (param.equalsIgnoreCase("java-fol"))
					//	_kb = new ClauseKb();
					//else if (param.equalsIgnoreCase("java-fol-dc-cwa"))
					//	_kb = new GroundKb(); // Does not seem to support incremental addition of facts, predicates?
					//else if (param.equalsIgnoreCase(""))
					//	_kb = new DemodClauseKb();
					//else if (param.equalsIgnoreCase(""))
					//	_kb = ; 
					else {
						_os.println("\nUnknown kb type '" + param + "', instantiating default 'ext-fol' Kb");
						_kb = new ClauseKb();
					}
				} else {
					_os.println("\nInstantiating default 'ext-fol' Kb");
					_kb = new ClauseKb();
				}

				// Print results
				_os.println("\nCreated new kb '" + _kb + "'.");
			}

			/***********************************************************
			 * Command: Tell
			 ***********************************************************/
			else if (_ci.command.type == FOL_TELL) {

				if (_ci.command.numParams() != 1) {
					_os.println("\nMust specify a single FOPC string as param.");
				} else {

					// Process the command
					_os.println();
					try {
						String query = _ci.command.getParam(0);
						String formula = FOPC.parse(query).toKIFString();
						_os.println("Adding KIF formula '" + formula + "' to "
								+ _kb);
						_kb.addFOPCFormula(query);
					} catch (Exception e) {
						// Just continue
					}
				}
			}

			/***********************************************************
			 * Command: Ask
			 ***********************************************************/
			else if (_ci.command.type == FOL_ASK) {

				if (_ci.command.numParams() != 1) {
					_os.println("\nMust specify a single FOPC string as param.");
				} else {

					// Process the command
					_os.println();
					try {
						String query = _ci.command.getParam(0);
						FOPC.Node query_fopc = FOPC.parse(query);
						String formula = query_fopc.toKIFString();
						_os.println("Asking KIF query: '" + formula + "' in "
								+ _kb);
						_os.println("\nResult: "
								+ (_kb.queryFOPC(query_fopc) ? "[TRUE - PROOF FOUND]"
										: "[PROOF NOT FOUND]"));
					} catch (Exception e) {
						// Just continue
					}
				}
			}

			/***********************************************************
			 * Command: Ask Bindings
			 ***********************************************************/
			else if (_ci.command.type == FOL_ASKB) {

				if (_ci.command.numParams() != 1) {
					_os.println("\nMust specify a single FOPC string as param.");
				} else {

					// Process the command
					_os.println();
					try {
						String query = _ci.command.getParam(0);
						FOPC.Node query_fopc = FOPC.parse(query);
						String formula = query_fopc.toKIFString();
						_os.println("Asking KIF query: '" + formula + "' in "
								+ _kb);
						BindingSet bs = _kb.queryFOPCBindings(query_fopc);
						_os.print("\nResult:\n-------\n" + bs);
					} catch (Exception e) {
						// Just continue
					}
				}
			}

		}
	}

}
