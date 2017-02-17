import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Properties;

import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;

import pddl4j.ErrorManager;
import pddl4j.InvalidExpException;
import pddl4j.PDDLObject;
import pddl4j.Parser;
import pddl4j.ErrorManager.Message;

public class Main_DimacsCNF {

	/**
	 * Display usage.
	 */
	private static void displayUsage() {
		System.out.println("Usage: Main_DimacsCNF [PDDL_DOMAIN] [PDDL_PROBLEM] [MAX_STATE]");
		System.exit(0);
	}

	public static void main(String[] args) {

		// Get the initial time when the program starts executing.
		long startTimeNano = System.nanoTime();
		
		Boolean satisf = false;
		int state = 1 ;
		ArrayList<Integer> timeList = new ArrayList<Integer>();
		long generalTime;
		
		// Checks the command line
		if (args.length != 3) {
				System.err.println("Invalid command line. "+ args.length);
				Main_DimacsCNF.displayUsage();	
		} else {
			// Creates an instance of the java pddl parser
			Properties pp = Parser.getDefaultOptions();
			Parser parser = new Parser(pp); 

			PDDLObject domain = null;

			try {
				File f = new File(args[0]);
				domain = parser.parse(f); 
			} catch (FileNotFoundException e) {
				System.err.println("Domain file not found, please check the file path.");
				Main_DimacsCNF.displayUsage();
			}

			PDDLObject problem = null;

			try {
				problem = parser.parse(new File(args[1]));
			} catch (FileNotFoundException e) {
				System.err.println("Problem file not found, please check the file path.");
				Main_DimacsCNF.displayUsage();
			}

			int max_state = 0;

			try {
				max_state = Integer.parseInt(args[2]);
			}catch (NumberFormatException e) {
				System.err.println("Max State should be a valid number.");
				Main_DimacsCNF.displayUsage();
			}

			PDDLObject obj = parser.link(domain, problem);
			// Gets the error manager of the pddl parser
			ErrorManager mgr = parser.getErrorManager();
			// If the parser produces errors we print it and stop
			if (mgr.contains(Message.ERROR)) {
				mgr.print(Message.ALL);
			} // else we print the warnings
			else {
				mgr.print(Message.WARNING);
				System.out.println("\nParsing domain \"" + domain.getDomainName()
						+ "\" done successfully ...");
				System.out.println("Parsing problem \"" + problem.getProblemName()
						+ "\" done successfully ...\n");
			}

			while (!satisf && (state <= max_state))/**for (int state = 1; state <= max_state; state++)**/{

			
			// We want to find a plan consisting of n=2 actions.
			STRIPS2SAT plugin = new STRIPS2SAT(obj,state);
			System.out.println("\n\nTry to solve in "+state+" states.");

			// Find all facts:
			plugin.initFacts();
			plugin.findTotalDimacsIdsFact();
			
			// Find all actions:
			try {
				plugin.initOps();
			} catch (InvalidExpException e) {
				e.printStackTrace();
			}

			// Find the goals:
			try {
				///////////////////
				plugin.initializeGoals();
				///////////////////
			} catch (InvalidExpException e1) {
				e1.printStackTrace();
			}
			
			/*
			////////////////////////////////////////////
			System.out.println("ACTIONS:");
			for (int x=0; x<plugin.ops_table_size; x++) {
				System.out.println(plugin.ops_table.get(x).getName());
			}
			System.out.println();
			System.out.println("FACTS:");
			for (int x=0; x<plugin.facts_table_size; x++) {
				System.out.println(plugin.facts_table.get(x));
			} 
			System.out.println();
			/////////////////////////////////////////////
			*/
			/*
            // Try to create of the dimacs file...
            try {
            	////////////////////////////
				plugin.create_cnf_file();
				////////////////////////////
			} catch (IOException e) {
				e.printStackTrace();
			}
			*/
			
			
			// BEGIN REGULER ENCODING
			try {
				//plugin.solveRegEncClassFrame();
				plugin.solveRegEncExplanFrame();
			} catch (ContradictionException e) {
				// Thrown by the solver if it finds out that 2 contradictory clauses have been generated.
				System.out.println();
				System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
				System.out.println("Contradictory clauses generated...");
				System.out.println();
				
//				System.exit(0);
			} catch (TimeoutException e) {
				// Thrown by the solver if the time given to search for a solution is exceeded.
				System.out.println("%%% THE PROBLEM SEEMS UNSATISFIABLE %%%");
				System.out.println("Sorry but time has ended...");
				System.out.println();
//				System.exit(0);
			}
			// END REGULAR ENCODING
			
			
			/*
			// BEGIN SIMPLE OPERATOR SPLITTING
			try {
				//plugin.solveSimpleOpSplittExplanFrame();
				//plugin.solveSimpleOpSplittExplanFrameFactoring();
				//plugin.solveSimpleOpSplittClassFrameFactoring();
				//plugin.solveOverloadOpSplittExplanFrameFactoring();
				//plugin.solveOverloadOpSplittClassFrameFactoring();
			} catch (ContradictionException e) {
				// Thrown by the solver if it finds out that 2 contradictory clauses have been generated.
				System.out.println();
				System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
				System.out.println("Contradictory clauses generated...");
				System.out.println();
			} catch (TimeoutException e) {
				// Thrown by the solver if the time given to search for a solution is exceeded.
				System.out.println("%%% THE PROBLEM SEEMS UNSATISFIABLE %%%");
				System.out.println("Sorry but time has ended...");
				System.out.println();
			}
			// END SIMPLE OPERATOR SPLITTING
			/////////////////////////////////////////////
			*/
			
			//TOTAL TIME			
			timeList.add(Integer.parseInt((System.nanoTime() - startTimeNano)/1000000+""));

			//end of the bigloop
			state++;
		}
		generalTime = 0;
		//Print the time for each try of the loop
		for (Integer time : timeList) {
			System.out.println("Partial Time = "+time+" ms");
			generalTime+=time;
		}
		System.out.println("\nTotal Time = "+ generalTime+" ms");
		}
	}
}
