import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import pddl4j.InvalidExpException;
import pddl4j.PDDLObject;
import pddl4j.exp.AndExp;
import pddl4j.exp.AtomicFormula;
import pddl4j.exp.Exp;
import pddl4j.exp.ExpID;
import pddl4j.exp.InitEl;
import pddl4j.exp.Literal;
import pddl4j.exp.NotAtomicFormula;
import pddl4j.exp.NotExp;
import pddl4j.exp.action.Action;
import pddl4j.exp.action.ActionDef;
import pddl4j.exp.action.ActionID;
import pddl4j.exp.fcomp.FCompExp;
import pddl4j.exp.term.Constant;
import pddl4j.exp.term.Substitution;
import pddl4j.exp.term.Term;
import pddl4j.exp.term.Variable;
import pddl4j.graphplan.Fact;
import pddl4j.graphplan.Op;

/**
 * Provides methods in order to:
 * 1) 	Parse a planning problem (expressed in PDDL format) and
 * 		create a PDDLObject object, with the help of the PDDL4J library.  
 * 2) 	Construct the corresponding Dimacs-CNF encoding of the problem, 
 * 		according to the encoding method chosen by the user.
 * 3) 	Solve the problem using the CNF solvers existing in the SAT4J library. 
 */
public class STRIPS2SAT 
{
	/**
	 * The planning problem we wish to solve which is the result of parsing the domain 
	 * and the specific problem, and then linking them.
	 */
	public PDDLObject problem;
	
	/**
	 *  goals[0] contains the positive preconditions of the goal.
	 *  goals[1] contains the negative preconditions of the goal.
	 */
	public BitSet[] goals;
	
	/**
	 * Contains all grounded facts of the problem.
	 */
	public ArrayList<Fact> facts_table;
	
	/**
	 * Contains all grounded actions (operations) of the problem.
	 */
	public ArrayList<Op> ops_table;
	
	/**
	 * The total number of grounded facts.
	 */
	public int facts_table_size;
	
	/**
	 * The total number of grounded actions (operations).
	 */
	public int ops_table_size;
	
	/**
	 * The maximum number of steps that the solution (plan) should contain.
	 */
	public int num_steps_inPlan;
	
	/**
	 * The string which contains the translation of our problem into Dimacs-CNF format.
	 * Used when we want to create a new text file containing the translation.
	 */
	public String solution;
	
	/**
	 * The file in which the solution (string in Dimacs-CNF format) will be stored.
	 */
	public File dimacs_cnf_file;
	
	/**
	 * The number of different Dimacs-Ids for all the facts at all timesteps.
	 */
	public int totalDimacsIdsFact;
	
	
	/**
	 * CONSTRUCTOR
	 * @param obj 
	 * 			The problem to solve expressed in the form of a PDDLObject
	 * @param num_steps
	 * 			The maximum number of steps that we accept in the solution.
	 */
	public STRIPS2SAT(PDDLObject obj, int num_steps) {

		this.problem = obj;
		this.solution = "";
		this.facts_table = new ArrayList<Fact>();
		this.ops_table = new ArrayList<Op>();
		this.facts_table_size = 0;
		this.ops_table_size = 0;
		this.num_steps_inPlan = num_steps;
		this.totalDimacsIdsFact= 0;	
	}
	
    /**
     * Properly stores the positive and negative preconditions of the goal
     * in the goals variable.
     */
    public void initializeGoals() throws InvalidExpException  {
    	goals = Utilities.expToBitSet(problem.getGoal(), facts_table);
    }
	
	//***************************************** "UTILITY" METHODS (BEGIN) *****************************************
	
	/**
     * Enumerates all the facts of the planning problem.
     */
	public void initFacts() {
        this.facts_table =  new ArrayList<Fact>(100);
        Iterator<AtomicFormula> i = this.problem.predicatesIterator();
        while (i.hasNext()) {
            AtomicFormula skeleton = i.next();
            //args corresponds to the current skeleton
            final List<Term> args = new ArrayList<Term>();
            for (Term arg: skeleton) {
                args.add(arg);
            }
            //args is built
            this.instantiateFacts(skeleton, args, new Substitution());
        }
        this.facts_table_size = this.facts_table.size();
    }
	
	/**
     * Instantiates all the fact from a specific atomic formula skeleton of the
     * problem.
     * 
     * @param skeleton the atomic formula skeleton to instantiate.
     * @param args the list of arguments of the atomic formula skeleton not yet
     *            instantiated.
     * @param sigma the map containing for each argument already instantiated its
     *            value.
     */
	// Called by the initFacts() function
	private void instantiateFacts(final AtomicFormula skeleton,
            						final List<Term> args,
            						final Substitution sigma) {
	    if (args.isEmpty()) {
	        final Fact fact = new Fact(skeleton.apply(sigma), this.facts_table.size());
	        this.facts_table.add(fact);
	    } else {
	        final Variable var = (Variable) args.get(0);
	        final Set<Constant> values = this.problem.getTypedDomain(var.getTypeSet());
	        for (Constant c : values) {
	            sigma.bind(var, c);
	            final List<Term> newArgs = new ArrayList<Term>(args);
	            @SuppressWarnings("unused")
				Term t = newArgs.remove(0);
	            this.instantiateFacts(skeleton, newArgs, sigma);
	        }
	    }
	}

	/**
     * Enumerates all the operators of the planning problem.
     * 
     * @throws InvalidExpException if an expression of an operator of the
     *             problem is not an accepted pddl expression.
     */
    public void initOps() throws InvalidExpException {
        // Generate the noop action first so a noop action as the same index as
        // its corresponding fact.
        	//for (int i = 0; i < this.facts_table_size; i++) {
        	//    this.addNewNoOp(this.facts_table.get(i));
        	//}
        //this.ops_index = this.ops_table.size();
        Iterator<ActionDef> i = this.problem.actionsIterator();
        while (i.hasNext()) {
            ActionDef a = i.next();
            if (a.getActionID().equals(ActionID.ACTION)) {
                Action op = (Action) a;
                List<Term> parameters = new ArrayList<Term>(op.getParameters());
                this.instantiateOps(op, parameters, new Substitution());
            } 
        }
        this.ops_table_size = this.ops_table.size();
    }
    
    /**
     * Instantiates all the operator from a specific action of the problem.
     * 
     * @param action the atomic formula skeleton to instantiate.
     * @param param the list of parameters of the action not yet instantiated.
     * @param sigma the map containing for each parameter already instantiated its
     *            value.
     * @throws InvalidExpException if an invalid pddl expression is found in
     *             the action.
     */
    private void instantiateOps(final Action action,
                final List<Term> param,
                final Substitution sigma)
                throws InvalidExpException {

        if (param.isEmpty()) {
            this.addNewOp(action, sigma);
        } else {
            final Variable var = (Variable) param.get(0);
            final Set<Constant> values = this.problem.getTypedDomain(var.getTypeSet());
            for (Constant c : values) {
                sigma.bind(var, c);
                final List<Term> newParam = new ArrayList<Term>(param);
                newParam.remove(0);
                this.instantiateOps(action, newParam, sigma);
            }
        }
    }
	
    /**
     * Add a new op created from a specific pddl action.
     * 
     * @param action the action.
     * @param sigma the mapping between the parameters and their values.
     * @return <code>true</code> if a new op is added; <code>false</code> otherwise.
     * @throws InvalidExpException if the unexpected pddl expression occurs in
     *             the action definition.
     */
    private boolean addNewOp(Action action, Substitution sigma)
                throws InvalidExpException {
        boolean added = false;
        AtomicFormula name = new AtomicFormula(action.getName());
        for (Term p : action.getParameters()) {
            name.add((Constant) sigma.getBinding((Variable) p));
        }
        BitSet[] pre = expToBitSet(action.getPrecondition().apply(sigma)); 
        if (pre != null) {
            BitSet[] eff = expToBitSet(action.getEffect().apply(sigma));
            Op op = new Op(name, pre[0], pre[1], eff[0], eff[1], this.ops_table.size());
            this.ops_table.add(op);
            added = true;
        } 
        return added;

    }

    /**
     * Transforms a pddl expression into a bit set representation.
     * 
     * @param exp the expression to transform.
     * @return a array of bit set with a length of 2 such the first bit set
     *         represents the positive fact of the expression and second bit set
     *         that represents the negative fact of the expression.
     * @throws InvalidExpException if an sub expression of the specified
     *             expression is not valid.
     */
    private BitSet[] expToBitSet(final Exp exp) 
            throws InvalidExpException {
        BitSet[] bitSet = new BitSet[2]; 
        bitSet[0] = new BitSet(this.facts_table_size);
        bitSet[1] = new BitSet(this.facts_table_size);
        HashSet<Literal> literals = null;
        
        literals = this.toLiteralSet(exp);
        if (literals != null) {
            for (Literal literal : literals) {
                if (literal.getExpID().equals(ExpID.ATOMIC_FORMULA)) {
                    AtomicFormula predicate = (AtomicFormula) literal;
                    final int index = this.facts_table.indexOf(predicate);
                    bitSet[0].set(index);
                } else {
                    NotAtomicFormula notExp = (NotAtomicFormula) literal;
                    AtomicFormula predicate = (AtomicFormula) notExp.getExp();
                    final int index = this.facts_table.indexOf(predicate);
                    bitSet[1].set(index);
                }
            }
        } else {
            bitSet = null;
        }
        return bitSet;
        
    }
    
    /**
     * Converts a ground pddl expression into a set of literals.
     * 
     * @param exp the expression that must be converted.
     * @return a set of literal that represents the specified expression.
     * @throws InvalidExpException if an sub expression of the specified
     *             expression is not valid.
     */
    private HashSet<Literal> toLiteralSet(final Exp exp) throws InvalidExpException {
        HashSet<Literal> literals = new HashSet<Literal>();

        Stack<Exp> stack = new Stack<Exp>();
        stack.add(exp);
        boolean failure = false;
        
        while (!stack.isEmpty() && !failure) {
            Exp e = stack.pop();
            switch (e.getExpID()) {
            case AND:
                AndExp andExp = (AndExp) e;
                for (Exp sexp : andExp) {
                    stack.push(sexp);
                }
                break;
            case ATOMIC_FORMULA:
                AtomicFormula p = (AtomicFormula) e;
                literals.add(p.clone());
                break;
            case F_COMP:
                FCompExp fcomp = (FCompExp) e;
                failure = !fcomp.evaluate();
                break;
            case NOT:
                NotExp notExp = (NotExp) e;
                Exp nexp = notExp.getExp();
                switch (nexp.getExpID()) {
                case F_COMP:
                    fcomp = (FCompExp) nexp;
                    failure = fcomp.evaluate();
                    break;
                default:
                    HashSet<Literal> pl = toLiteralSet(notExp.getExp());
                    if (pl != null) {
                        for (Literal l : pl) {
                            NotAtomicFormula f = new NotAtomicFormula((AtomicFormula) l);
                            literals.add(f);
                        }
                     } else {
                       failure = true;
                     }
                }
                break;
            default:
                throw new InvalidExpException(exp.getExpID());
            }
        }
        return failure ? null : literals;    
    }
    
   //***************************************** "UTILITY" METHODS (END) *****************************************
										
    
   /**
    * Creates a new file in which we will write the Dimacs-CNF encoding of the problem.
    * @throws IOException
    */
    public void create_cnf_file() throws IOException{
    	String filename = problem.getDomainName() + "_" + problem.getProblemName();
        dimacs_cnf_file = new File(filename);
        if(!dimacs_cnf_file.exists()){
        	dimacs_cnf_file.createNewFile();
        	System.out.println("New file \"dimacs-CNF_encoding.cnf\" has been created " 
                              	+ "to the current directory, which is: "
                              	+ dimacs_cnf_file.getCanonicalPath());
        	System.out.println();
        }
        create_DimacsCNF_string();
        write_cnf_file();
    }

	/**
     * This method writes the string containing the solution into the file. 
     * @throws IOException
     */
    public void write_cnf_file() throws IOException{
    	BufferedWriter output = new BufferedWriter(new FileWriter(dimacs_cnf_file));
    	output.write(solution);
    	output.close();
    }
    
    /**
     * Finds the Dimacs-CNF expression that corresponds to our problem.
     * It uses the Regular Encoding for the Actions, the Explanatory Frame Axioms,
     * and the Complete Exclusion Axioms.
     * @return
     * 		the solution in Dimacs-CNF format.
     */
    public String create_DimacsCNF_string() {
    	// The number of clauses contained in the string solution.
    	int num_of_clauses = 0;
    	
    	// Beginning of the file...
    	solution = " c  This automatically generated file contains" 
    			+ " the Dimacs-CNF format for the following context:" + "\r\n" 
    			+ " c  Domain: " + problem.getDomainName() + "\r\n"
    			+ " c  Problem: " + problem.getProblemName() + "\r\n"
    			+ " p cnf " + findTotalDimacsIdsRegularEncoding() + "\r\n ";
    	
    	// STAGE 1 (Initial State):
    	// First we create the lines in the file that correspond to the Initial State of the problem.
    	// The initial state has no "negative" statements, because everything that is not explicitly declared true is false.
    	// We are in time step --> 0
    	
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...
        		if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
        			solution = solution + findDimacsIdFact(i, 0) + " 0\r\n ";
        			num_of_clauses++;
        			isInit = true ;
        			continue;
        		} 
    		}
    		if (!isInit){
    			solution = solution + (-findDimacsIdFact(i, 0)) + " 0\r\n ";
    			num_of_clauses++;
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	// Lines in the file corresponding to the Goal State.
    	// We have: time step --> last time step 
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			solution = solution + findDimacsIdFact(i, num_steps_inPlan) + " 0\r\n ";
    			num_of_clauses++;
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			solution = solution + (-findDimacsIdFact(i, num_steps_inPlan)) + " 0\r\n ";
    			num_of_clauses++;
    		}
    	}
    	
    	// STAGE 3 (Definition of actions - Regular Encoding):
    	// Lines in the file corresponding to the schema: Action --> Preconds + Effects
    	// (NOT(action) OR precond1) AND (NOT(action) OR precond2) AND ... AND (not(action) OR precondM)
    	// AND
    	// (NOT(action) OR effect1) AND (NOT(action) OR effect2) AND ... AND (NOT(action) OR effectN)
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			String operationCode = Integer.toString(-findDimacsIdOperationRegularEncoding(i, j));
    			bs = ops_table.get(i).getPositivePreconditon(); 
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					solution = solution + operationCode + " " +
							findDimacsIdFact(k, j) + " 0\r\n ";
    					num_of_clauses++;
    				}
    			}
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					solution = solution + operationCode + " " +
							(-findDimacsIdFact(k, j)) + " 0\r\n ";
    					num_of_clauses++;
    				}
    			}
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					solution = solution + operationCode + " " +
							findDimacsIdFact(k, j+1) + " 0\r\n ";
    					num_of_clauses++;
    				}
    			}
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					solution = solution + operationCode + " " +
							(-findDimacsIdFact(k, j+1)) + " 0\r\n ";
    					num_of_clauses++;
    				}
    			}
    		}	
    	}
    	
    	// STAGE 4 (Explanatory Frame Axioms):
    	// Lines in the file corresponding to the schema:
    	// (FactA_timestepN) AND (NOT(FactA_timestepN+1)) --> Action_timestepN (which is a possible cause),
    	// (NOT(FactA_timestepN)) AND (FactA_timestepN+1) --> Action_timestepN (which is a possible cause).
    	boolean isEffect = false;
    	for (int i=0; i<facts_table_size; i++) {
    		for (int j=0; j<ops_table_size; j++) {
    			if (ops_table.get(j).getPositiveEffect().get(i)) {
    				isEffect = true;
    			}
    		}
    		// If we found out that for a specific fact, there exists at least one action that has it as
    		// a POSITIVE EFFECT, then we will have to add new clauses to the solution.
    		// The pattern is:
    		// 		FactA OR (NOT FactB) OR ActionA OR ActionB OR ...
    		if (isEffect) {
    			for (int t=0; t<get_numTimeSteps(); t++) {
    				solution = solution + findDimacsIdFact(i, t) + " " +
						(-findDimacsIdFact(i, t+1));
    				for (int j=0; j<ops_table_size; j++) {
    	    			if (ops_table.get(j).getPositiveEffect().get(i)) {
    	    				solution = solution + " " + findDimacsIdOperationRegularEncoding(j, t); 
    	    			}
    	    		}
    				solution = solution + " 0\r\n ";
    				num_of_clauses++;
    			}
    		}					
    	}	
    	isEffect = false;
    	for (int i=0; i<facts_table_size; i++) {
    		for (int j=0; j<ops_table_size; j++) {
    			if (ops_table.get(j).getNegativeEffect().get(i)) {
    				isEffect = true;
    			}
    		}
    		// If we found out that for a specific fact, there exists at least one action that has it as
    		// a negative effect, then we will have to add new clauses to the solution.
    		// The pattern is:
    		// 		(NOT FactA) OR FactB OR ActionA OR ActionB OR ...
    		if (isEffect) {
    			for (int t=0; t<get_numTimeSteps(); t++) {
    				solution = solution + (-findDimacsIdFact(i, t)) + " " +
						findDimacsIdFact(i, t+1);
    				for (int j=0; j<ops_table_size; j++) {
    	    			if (ops_table.get(j).getNegativeEffect().get(i)) {
    	    				solution = solution + " " + findDimacsIdOperationRegularEncoding(j, t); 
    	    			}
    	    		}
    				solution = solution + " 0\r\n ";
    				num_of_clauses++;
    			}
    		}					
    	}
    	
    	// STAGE 5 (Complete Exclusion Axioms):
    	// Two actions cannot be executed in the same timestep.
    	for (int i=0; i<get_numTimeSteps(); i++) {
    		for (int j=0; j<ops_table_size; j++) {
    			for (int k=j+1; k<ops_table_size; k++) {
    				solution = solution + (-findDimacsIdOperationRegularEncoding(j, i)) + " " +
    					(-findDimacsIdOperationRegularEncoding(k, i)) + " 0\r\n ";
    				num_of_clauses++;
    			}
    		}	
        }

    	// Adds the number of clauses in the proper place at the string (p cnf num_vars num_clauses)
    	this.addNumOfClauses(num_of_clauses);
    	
		return solution;
    }
    
    /**
     * Adds the number of clauses in the beginning of the solution string.
     * @param number_of_clauses
     */
    private void addNumOfClauses(int number_of_clauses) {
    	String temp = solution;
		int cut = 0;
		int cutsum = 0;
		for (int i=0; i<4; i++) {
			cut = temp.indexOf("\r\n");
			cutsum += cut+2;
			temp = temp.substring(cut+2);
		}
		solution = solution.substring(0, cutsum-2) + " " + number_of_clauses + "\r\n" + temp;
	}
    
    /**
     * Finds and displays a solution to our problem, provided that there exists one.
     * Otherwise, it declares the problem unsatisfiable.
     * The sat4j library is used to find the solution.
     * It uses the Regular Encoding of Actions,
     * as well as the Explanatory Frame Axioms and the Complete Exclusion Axioms.
     * @return
     * @throws ContradictionException 
     * @throws TimeoutException 
     */
    public void solveRegEncExplanFrame() throws ContradictionException, TimeoutException {
    	final int MAXVAR = 1000000;
		final int NBCLAUSES = 500000;
		
		// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
		int[] mysolution = null;
		
		ISolver solver = SolverFactory.newDefault();
		//  prepare the solver to accept MAXVAR variables. MANDATORY
		solver.newVar(MAXVAR);
		// not mandatory for SAT solving. MANDATORY for MAXSAT solving
		solver.setExpectedNumberOfClauses(NBCLAUSES);
		// Feed the solver using Dimacs format, using arrays of int
		// (best option to avoid dependencies on SAT4J IVecInt)
		
		/**
		 * We will use this variable in order to build all necessary clauses (one by one).
		 */
		VecInt clause;
    	
    	// STAGE 1 (Initial State):
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...
    		
        		if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
        			clause = new VecInt(new int[]{findDimacsIdFact(i, 0)});
        			solver.addClause(clause);
        			isInit = true ;
        			continue;
        		} 
    		}
    		if (!isInit){
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, 0)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 3 (Definition of actions - Regular Encoding):
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			int operationCode = -findDimacsIdOperationRegularEncoding(i, j);
    			bs = ops_table.get(i).getPositivePreconditon();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, findDimacsIdFact(k, j)});
    	    			solver.addClause(clause);
    				}
    			}
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, -findDimacsIdFact(k, j)});
    					solver.addClause(clause);
    				}
    			}
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, findDimacsIdFact(k, j+1)});
    					solver.addClause(clause);
    				}
    			}
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, -findDimacsIdFact(k, j+1)});
    					solver.addClause(clause);
    				}
    			}
    		}	
    	}
    	
    	// STAGE 4 (Explanatory Frame Axioms):
    	ArrayList<Integer> sol;
    	// Check the POSITIVE EFFECTS OF ACTIONS
    	for (int i=0; i<facts_table_size; i++) {
    		for (int t=0; t<get_numTimeSteps(); t++) {
    			sol = new ArrayList<Integer>();
    			sol.add(findDimacsIdFact(i, t));
    			sol.add(-findDimacsIdFact(i, t+1));
    			for (int j=0; j<ops_table_size; j++) {
    				if (ops_table.get(j).getPositiveEffect().get(i)) {
    					sol.add(findDimacsIdOperationRegularEncoding(j, t)); 
    				}
    			}
    			// Create the array from the ArrayList
    			int[] mat = new int[sol.size()];
    			for (int l=0; l<sol.size(); l++) {
    				mat[l] = sol.get(l);	
    			}
    			// Add the found clause to the solution
    			clause = new VecInt(mat);
    			solver.addClause(clause);
    		}			
    	}	
    	sol = new ArrayList<Integer>();
    	// Check the NEGATIVE EFFECTS OF ACTIONS
    	for (int i=0; i<facts_table_size; i++) {
    		for (int t=0; t<get_numTimeSteps(); t++) {
    			sol = new ArrayList<Integer>();
    			sol.add(-findDimacsIdFact(i, t));
    			sol.add(findDimacsIdFact(i, t+1));
    			for (int j=0; j<ops_table_size; j++) {
    				if (ops_table.get(j).getNegativeEffect().get(i)) {
    					sol.add(findDimacsIdOperationRegularEncoding(j, t));
    				}
    			}
    			int[] mat = new int[sol.size()];
    			for (int l=0; l<sol.size(); l++) {
    				mat[l] = sol.get(l);
    			}
    			clause = new VecInt(mat);
    			solver.addClause(clause);
    		}				
    	}
    	
    	// STAGE 5 (Complete Exclusion Axioms):
    	for (int i=0; i<get_numTimeSteps(); i++) {
    		for (int j=0; j<ops_table_size; j++) {
    			for (int k=j+1; k<ops_table_size; k++) {
    				clause = new VecInt(new int[]{-findDimacsIdOperationRegularEncoding(j, i),
    												-findDimacsIdOperationRegularEncoding(k, i)});
					solver.addClause(clause);
    			}
    		}	
        }
    	
    	IProblem problem = solver;
    	// We create a table of integers which holds the solution (if there is one).
		// It contains positive and negative integers.
    	mysolution = problem.findModel();
    	
		if (mysolution != null) {
			System.out.println("*** THE PROBLEM IS SATISFIABLE! ***");
			System.out.println();
			System.out.println("The proposed solution is the following:");
			System.out.println();
			
			// We translate the solution into an understandable form of a plan.
			this.translateSolutionRegularEncoding(mysolution);
			
			
        } else {
            System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
        }
		
		return;
    } 
    
    /**
     * Finds and displays a solution to our problem, provided that there exists one.
     * Otherwise, it declares the problem unsatisfiable.
     * The sat4j library is used to find the solution.
     * It uses the Regular Encoding of actions,
     * as well as the Classical Frame Axioms, followed by the At-Least-One Axioms.
     * @return
     * @throws ContradictionException 
     * @throws TimeoutException 
     */
    public void solveRegEncClassFrame() throws ContradictionException, TimeoutException {
    	
    	final int MAXVAR = 1000000;
		final int NBCLAUSES = 500000;
		
		// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
		int[] mysolution = null;
		
		ISolver solver = SolverFactory.newDefault();
		//  prepare the solver to accept MAXVAR variables. MANDATORY
		solver.newVar(MAXVAR);
		// not mandatory for SAT solving. MANDATORY for MAXSAT solving
		solver.setExpectedNumberOfClauses(NBCLAUSES);
		// Feed the solver using Dimacs format, using arrays of int
		// (best option to avoid dependencies on SAT4J IVecInt)
		
		/**
		 * We will use this variable in order to build all necessary clauses (one by one).
		 */
		VecInt clause;
    	
    	// STAGE 1 (Initial State):
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...
    		
        		if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
        			clause = new VecInt(new int[]{findDimacsIdFact(i, 0)});
        			solver.addClause(clause);
        			isInit = true ;
        			continue;
        		} 
    		}
    		if (!isInit){
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, 0)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 3 (Definition of Actions - Regular Encoding):
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			int operationCode = -findDimacsIdOperationRegularEncoding(i, j);
    			bs = ops_table.get(i).getPositivePreconditon();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, findDimacsIdFact(k, j)});
    	    			solver.addClause(clause);
    				}
    			}
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, -findDimacsIdFact(k, j)});
    					solver.addClause(clause);
    				}
    			}
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, findDimacsIdFact(k, j+1)});
    					solver.addClause(clause);
    				}
    			}
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					clause = new VecInt(new int[]{operationCode, -findDimacsIdFact(k, j+1)});
    					solver.addClause(clause);
    				}
    			}
    		}	
    	}
    	
    	// STAGE 4A (Classical Frame Axioms):
    	// If fluentF is not an effect of actionA, then:
    	// fluentF_i AND actionA_i --> fluentF_i+1  ======>  (NOT fluentF_i) OR (NOT actionA_i) OR fluentF_i+1
    	// (NOT fluentF_i) AND actionA_i --> (NOT fluentF_i+1)  ======>  fluentF_i OR (NOT actionA_i) OR (NOT fluentF_i+1)
    	// We will create clauses for each action which will impose that fluents not belonging
    	// to the effects of the action must remain the same after the action's execution.
    	for (int i=0; i<ops_table_size; i++) {
    		Op curr = ops_table.get(i);
    		BitSet posEff = null;
			BitSet negEff = null;
 			// find the action's effects
			posEff = curr.getPositiveEffect();
			negEff = curr.getNegativeEffect();
			for (int j=0; j<facts_table_size; j++) {
				// If the fact is neither in the current action's positive effects,
				// nor in its negative effects, we should build a clause for the 
				// classical frame axiom. 
				if ( !posEff.get(j) && !negEff.get(j)) {
					for (int k=0; k<num_steps_inPlan; k++) {
						clause = new VecInt(new int[]{-findDimacsIdFact(j, k) , 
														-findDimacsIdOperationRegularEncoding(i, k),
														findDimacsIdFact(j, k+1)});
						solver.addClause(clause);
						clause = new VecInt(new int[]{findDimacsIdFact(j, k) , 
														-findDimacsIdOperationRegularEncoding(i, k),
														-findDimacsIdFact(j, k+1)});
						solver.addClause(clause);
					}
				}
    		}
    	}
    	
    	// STAGE 4B (At-Least-One Axioms):
    	// At each timestep, at least one action has to be executed.
    	// With these axioms we avoid non-intended models (false plans). 
    	for (int i=0; i<num_steps_inPlan; i++) {
    		int[] mat = new int[ops_table_size];
    		// for each action...
    		for (int j=0; j<ops_table_size; j++) {
    			mat[j] = findDimacsIdOperationRegularEncoding(j, i);
    		}
    		clause = new VecInt(mat);
    		solver.addClause(clause);
    	}
    	
    	IProblem problem = solver;
    	// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
    	mysolution = problem.findModel();
    	
		if (mysolution != null) {
			System.out.println("*** THE PROBLEM IS SATISFIABLE! ***");
			System.out.println();
			System.out.println("The proposed solution is the following:");
			System.out.println();
			
			// We translate the solution into an understandable form of a plan.
			this.translateSolutionRegularEncoding(mysolution);
			
        } else {
            System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
        }
		
		return;
    } 
    
    /**
     * Finds and displays a solution to our problem, provided that there exists one.
     * Otherwise, it declares the problem unsatisfiable.
     * The sat4j library is used to find the solution.
     * Encodes the actions of the problem using the method of Simple-Operator-Splitting.
     * It also uses the Explanatory Frame Axioms and the Complete Exclusion Axioms.
     * It does not use factoring, therefore it is impractical!
     * 
     * @throws ContradictionException, TimeoutException 
     */
    public void solveSimpleOpSplittExplanFrame() throws ContradictionException, TimeoutException {

    	final int MAXVAR = 1000000;
		final int NBCLAUSES = 500000;
		
		ISolver solver = SolverFactory.newDefault();
		// prepare the solver to accept MAXVAR variables. MANDATORY
		solver.newVar(MAXVAR);
		// not mandatory for SAT solving. MANDATORY for MAXSAT solving
		solver.setExpectedNumberOfClauses(NBCLAUSES);
		// Feed the solver using Dimacs format, using arrays of int
		// (best option to avoid dependencies on SAT4J IVecInt)
		
		/**
		 * We will use this variable in order to build all necessary clauses (one by one).
		 */
		VecInt clause;
    	
    	// STAGE 1 (Initial State):
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...
        		if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
        			clause = new VecInt(new int[]{findDimacsIdFact(i, 0)});
        			solver.addClause(clause);
        			isInit = true ;
        			continue;
        		} 
    		}
    		if (!isInit){
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, 0)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// Stage 3 (Actions Encoding - SIMPLE OPERATOR SPLITTING):
    	// The basic ArrayList (encodingAllActionsHelper) which contains an ArrayList for each action with a different name.
    	// For example, in the blocksworld, we have the basic ArrayList (encodingAllActionsHelper) that contains 4 ArrayLists,
    	// which correspond to the actions: pickup, putdown, stack and unstack.
    	ArrayList<ArrayList<HashMap<Term, Integer>>> encodingAllActionsHelper = new ArrayList<ArrayList<HashMap<Term, Integer>>>();
    	// We remember the name of the previous action, in order to avoid creating a new ArrayList for the next action
    	// if the two share the same name.
    	String previousOpName = "";
    	// Each time that this ArrayList is properly built, it represents an action with a specific name (eg. stack).
    	// These ArrayLists are the elements of the encodingAllActionsHelper ArrayList.
    	ArrayList<HashMap<Term, Integer>> encodingOneActionHelper = null;
    	// This variable will be equal to the total number of different ints that are used in order to
    	// encode all split actions of a same timestep.
    	// It is used in every step in order to give a different encoding number to a (split) action.
    	int dimacsNum = 0;
    	// The encodedActions ArrayList will be used in the following way:
    	// Each element is an ArrayList that corresponds to a grounded action for the first timestep.
    	// Those (inner) ArrayLists contain the dimacs numbers of that grounded action (for the first timestep).
    	// The encoding of actions of other timesteps is based on this ArrayList,
    	// so we don't need to generate any other ArrayLists.
    	ArrayList<ArrayList<Integer>> encodedActions = new ArrayList<ArrayList<Integer>>();
    	
    	// The inner ArrayList that contains the dimacs numbers of a grounded action.
    	ArrayList<Integer> encoded = null;
    	
    	// We have to test for each grounded action, if there is the need to create an (encoded) ArrayList.
    	for (int i=0; i<ops_table_size; i++) {
    		
    		Op currOp = ops_table.get(i);
    		int OpArity = currOp.getName().getArity();
    		// As we are proceeding to the construction of the hashmaps, in the same time,
    		// we will encode each action by associating it with an ArrayList of integers
    		encoded = new ArrayList<Integer>(); 
    		
    		// If we got an action with a different name than the previous,
    		// then we must create an ArrayList of HashMaps for this new action
    		if ( !currOp.getName().getPredicate().toString().equals(previousOpName) ) {
    			// remember for next iteration...
    			previousOpName = currOp.getName().getPredicate().toString();
    			// Create the ArrayList for this action.
    			encodingOneActionHelper = new ArrayList<HashMap<Term, Integer>>();
    			for (int j=0; j<OpArity; j++) {
    				encodingOneActionHelper.add(new HashMap<Term, Integer>());
    			}
    			// Continue the "construction" of the basic ArrayList (encodingAllActionsHelper).
    			encodingAllActionsHelper.add(encodingOneActionHelper);
    		}
    		// Now for each term of the currOp we have to find a corresponding number, with the help of 
    		// the corresponding HashMap, and (if it is a new one) we have to add this correspondence
    		// to the HashMap.
    		Iterator<Term> it = currOp.getName().iterator();
    		int index = 0;
    		
    		while (it.hasNext()) {
    			// Check the proper HashMap. If the key has been used we can use its corresponding value.
    			// If there is no such key, we insert a new pair in the HashMap.
    			HashMap<Term, Integer> hmap = encodingOneActionHelper.get(index);
    			Term key = (Term)it.next();
    			if ( !hmap.containsKey(key) ) {
    				dimacsNum++;
    				hmap.put(key, dimacsNum);
    				encoded.add(totalDimacsIdsFact + dimacsNum);	
    			} else {
    				encoded.add(totalDimacsIdsFact + hmap.get(key));
    			}
    			index++;	
			} // end-while
    		encodedActions.add(encoded);
    	} // end-for (each action)
    	// We can now save the size of the ArrayList we constructed in order to use it later.
    	int encodedActionsSize = encodedActions.size();
    	
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			//  For the POSITIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getPositivePreconditon();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					int[] mat = new int[encodedActions.get(i).size()+1];
        				for (int l=0; l<encodedActions.get(i).size(); l++) {
        					mat[l] = -( (Integer) encodedActions.get(i).get(l) + dimacsNum*j );	
        				}
        				mat[encodedActions.get(i).size()] = findDimacsIdFact(k, j);
        				clause = new VecInt(mat);
            			solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					int[] mat = new int[encodedActions.get(i).size()+1];
        				for (int l=0; l<encodedActions.get(i).size(); l++) {
        					mat[l] = -( (Integer) encodedActions.get(i).get(l) + dimacsNum*j );	
        				}
        				mat[encodedActions.get(i).size()] = -findDimacsIdFact(k, j);
        				clause = new VecInt(mat);
        				solver.addClause(clause);
    				}
    			}
    			//  For the POSITIVE EFFECTS of actions...
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					int[] mat = new int[encodedActions.get(i).size()+1];
        				for (int l=0; l<encodedActions.get(i).size(); l++) {
        					mat[l] = -( (Integer) encodedActions.get(i).get(l) + dimacsNum*j );	
        				}
        				mat[encodedActions.get(i).size()] = findDimacsIdFact(k, j+1);  // Attention, must be "+1"!
        				clause = new VecInt(mat);
        				solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE EFFECTS of actions...
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					int[] mat = new int[encodedActions.get(i).size()+1];
        				for (int l=0; l<encodedActions.get(i).size(); l++) {
        					mat[l] = -( (Integer) encodedActions.get(i).get(l) + dimacsNum*j );	
        				}
        				mat[encodedActions.get(i).size()] = -findDimacsIdFact(k, j+1);  // Attention, must be "+1"!
        				clause = new VecInt(mat);
        				solver.addClause(clause);
    				}
    			}
    		}	
    	}
    	
    	// STAGE 4 (Explanatory Frame Axioms):
    	// For the POSITIVE EFFECTS OF ACTIONS, and also,
    	// for the NEGATIVE EFFECTS OF ACTIONS.
    	for (int i=0; i<facts_table_size; i++) {
    		// The actionsWithPosEff ArrayList contains (in the form of ArrayLists) all the actions
    		// which have the current fact to their POSITIVE EFFECTS.
    		ArrayList<ArrayList<Integer>> actionsWithPosEff = new ArrayList<ArrayList<Integer>>();
    		// The actionsWithNegEff ArrayList contains (in the form of ArrayLists) all the actions
    		// which have the current fact to their NEGATIVE EFFECTS.
    		ArrayList<ArrayList<Integer>> actionsWithNegEff = new ArrayList<ArrayList<Integer>>();
    		// Fill the ArrayLists we just created with the proper data.
    		for (int j=0; j<ops_table_size; j++) {
    			// build the Arraylist for the positive effects.
    			if (ops_table.get(j).getPositiveEffect().get(i)) {
    				
    				actionsWithPosEff.add(encodedActions.get(j));	
    			}
    			// build the Arraylist for the negative effects.
    			if (ops_table.get(j).getNegativeEffect().get(i)) {
    				actionsWithNegEff.add(encodedActions.get(j));	
    			}
    		}
    		// (end-for) end of construction of actionsWithPosEff and actionsWithNegEff (for the current fact).
    		
    		// The following "set of pointers" will help us find the result we search for.
    		// In order to encode the positive effects of actions we will have to obtain
    		// all the possible combinations of basic elements of the actionsWithPosEff ArrayList.
    		// The pointers[] variable will help accomplish this task.
    		// It contains actionsWithPosEff.size() "pointers",
    		// one for every action of the actionsWithPosEff ArrayList.
    		int[] pointers;
    		if (actionsWithPosEff.size()==0) {
    			pointers = null;
    		} else {
	    		pointers = new int[actionsWithPosEff.size()];
	    		for (int j=0; j<pointers.length; j++) {
	    			pointers[j] = 0;
	    		}
    		}
    		// If there is a "pointer" which is not "depleted", then
    		// the value of the respective boolean variable will have to be true; 
    		boolean posEffPointerNotDepleted;
    		boolean negEffPointerNotDepleted;
    		
    		// For each timestep... 
    		for (int t=0; t<num_steps_inPlan; t++) {
    			ArrayList<Integer> res = new ArrayList<Integer>();
    			
    			posEffPointerNotDepleted = true;
    			// A loop will give a different combination of the inner elements,
    			// which is a clause on the dimacs format.
    			while (posEffPointerNotDepleted) {
    				// The resulting piece of info needed for the solver.
    				// We don't compute the number of combinations, so we use an ArrayList.
    				// At the end, we will construct an int[] from this ArrayList.
    				res = new ArrayList<Integer>();
    				// Put the fact we are examining (POS - NEG: Because of negation...)
    				res.add(findDimacsIdFact(i, t));
    				res.add(-findDimacsIdFact(i, t+1));
    				// Put the current combination using the pointers[] variable.
    				if (pointers != null) {
    					for (int k=0; k<pointers.length; k++) {
    						res.add( (Integer)actionsWithPosEff.get(k).get(pointers[k]) + dimacsNum*t);
    					}
    					// Now we have to manipulate the pointers[] in order to be ready 
    					// to get the next combination in the next loop of the while,
    					// or to realise that there exist no more combinations. So...
    					// IF THE FIRST POINTER HAS REACHED ITS END...
    					if (pointers[0]==actionsWithPosEff.get(0).size()-1) {
    						// We reset the pointer to (0).
    						pointers[0] = 0;
    						// Now, work for the other pointers...
    						// If the following for loop doesn't change the value of the boolean variable,
    						// that means that all combinations have been computed
    						// (we are in the last combination).
    						posEffPointerNotDepleted = false;
    						for (int m=1; m<pointers.length && !posEffPointerNotDepleted; m++) {
    							// Reset to zero only pointers which form a "group"
    							// after the first pointer.
    							if (pointers[m] == actionsWithPosEff.get(m).size()-1) {
    								pointers[m] = 0;
    							}
    							else  { // if another pointer has not been depleted
    								// properly set its value.
    								pointers[m]++;
    								// We want to be able to continue the while loop.
    								posEffPointerNotDepleted = true;
    							}
    						}
    					} else { // We increase the number of the first pointer
    						pointers[0]++;
    					}
    				} else {
    					posEffPointerNotDepleted = false;
    				}
    				// Put the result we found into a clause and add it to the solver.
    				int[] mat = new int[res.size()];
    				for (int x=0; x<res.size(); x++) {
    					mat[x] = (Integer)res.get(x);
    				}
    				clause = new VecInt(mat);
        			solver.addClause(clause);
    			} //end-while
    				
    			// Then do the NEGATIVE EFFECTS OF ACTIONS.
    			if (actionsWithNegEff.size()==0) {
        			pointers = null;
        		} else {
    	    		pointers = new int[actionsWithNegEff.size()];
    	    		for (int j=0; j<pointers.length; j++) {
    	    			pointers[j] = 0;
    	    		}
        		}
    			negEffPointerNotDepleted = true;
    			while (negEffPointerNotDepleted) {
    				res = new ArrayList<Integer>();
    				// Put the fact we are examining (NEG - POS: Because of negation...)
    				res.add(-findDimacsIdFact(i, t));
    				res.add(findDimacsIdFact(i, t+1));
    				if (pointers != null) {
    					// Put the current combination using the pointers[] variable.
    					for (int k=0; k<pointers.length; k++) {
    						res.add((Integer)actionsWithNegEff.get(k).get(pointers[k]) + dimacsNum*t);
    					}
    					if (pointers[0]==actionsWithNegEff.get(0).size()-1) {
    						// We reset the pointer to (0).
    						pointers[0] = 0;
    						// Now, work for the other pointers...
    						negEffPointerNotDepleted = false;
    						for (int m=1; m<pointers.length && !negEffPointerNotDepleted; m++) {
    							// Reset to zero only pointers which form a "group"
    							// after the first pointer.
    							if (pointers[m] == actionsWithNegEff.get(m).size()-1) {
    								pointers[m] = 0;
    							}
    							else  { // if another pointer has not been depleted
    								// properly set its value.
    								pointers[m]++;
    								// We want to be able to continue the while loop.
    								negEffPointerNotDepleted = true;
    							}
    						}
    					} else { // We increase the number of the first pointer
    						pointers[0]++;
    					}
    				} else {
    					negEffPointerNotDepleted = false;
    				}
    				// Put the result we found into a clause and add it to the solver.
    				int[] mat= new int[res.size()];
    				for (int x=0; x<res.size(); x++) {
    					mat[x] = (Integer)res.get(x);
    				}
    				clause = new VecInt(mat);
        			solver.addClause(clause);
    			} //end-while
    		}// end-for (each timestep)
    	}// end-for (each fact)
    	
    	// STAGE 5 (Complete Exclusion Axioms):
    	for (int t=0; t<num_steps_inPlan; t++) { // do for every timestep
    		// No two actions can happen at the same time.
    		for (int i=0; i<encodedActionsSize; i++) {
    			for (int j=i+1; j<encodedActionsSize; j++) {

    				ArrayList<Integer> a = encodedActions.get(i);
    				ArrayList<Integer> b = encodedActions.get(j);

    				int[] mat = new int[a.size() + b.size()];
    				// Fill the clause with half of its data
    				for (int l=0; l<a.size(); l++) {
    					mat[l] = -((Integer)a.get(l) + dimacsNum*t);
    				}
    				// Fill the clause with the other half of its data
    				for (int l=0; l<b.size(); l++) {
    					mat[a.size()+l] = -((Integer)b.get(l)+ dimacsNum*t);
    				}
    				clause = new VecInt(mat);
    				solver.addClause(clause);
    			}
    		}
    	}
    	
    	// SOLVER 
    	IProblem problem = solver;
    	
    	int[] mysolution = null;
    	// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
    	mysolution = problem.findModel();
    	
		if (mysolution != null) {
			System.out.println("*** THE PROBLEM IS SATISFIABLE! ***");
			System.out.println();
			System.out.println("The proposed solution is the following:");
			System.out.println();
			
			// We translate the solution into an understandable form of a plan.
			this.translateSolutionOperatorSplitting(mysolution, dimacsNum, encodedActions);
			
        } else {
            System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
        }
		
    	return;
    }
    
    /**
     * Finds and displays a solution to our problem, provided that there exists one.
     * Otherwise, it declares the problem unsatisfiable.
     * The sat4j library is used to find the solution.
     * Encodes the actions of the problem using the method of Simple-Operator-Splitting.
     * It also uses the Explanatory Frame Axioms and the Complete Exclusion Axioms.
     * It implements the technique of factoring, in order to avoid combinatorial explosion when
     * trying to convert clauses into CNF.
     * 
     * @throws ContradictionException, TimeoutException 
     */
    public void solveSimpleOpSplittExplanFrameFactoring() throws ContradictionException, TimeoutException {
    	
    	final int MAXVAR = 1000000;
    	final int NBCLAUSES = 500000;

    	ISolver solver = SolverFactory.newDefault();
    	// prepare the solver to accept MAXVAR variables. MANDATORY
    	solver.newVar(MAXVAR);
    	// not mandatory for SAT solving. MANDATORY for MAXSAT solving
    	solver.setExpectedNumberOfClauses(NBCLAUSES);
    	// Feed the solver using Dimacs format, using arrays of int
    	// (best option to avoid dependencies on SAT4J IVecInt)

    	/**
    	 * We will use this variable in order to build all necessary clauses (one by one).
    	 */
    	VecInt clause;

    	// STAGE 1 (Initial State):
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...

    			if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
    				clause = new VecInt(new int[]{findDimacsIdFact(i, 0)});
    				solver.addClause(clause);
    				isInit = true ;
    				continue;
    			} 
    		}
    		if (!isInit){
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, 0)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// Stage 3 (Actions Encoding - SIMPLE OPERATOR SPLITTING - Factored):
    	// The basic ArrayList (encodingAllActionsHelper) which contains an ArrayList for each action with a different name.
    	// For example, in the blocksworld, we have the basic ArrayList (encodingAllActionsHelper) that contains 4 ArrayLists,
    	// which correspond to the actions: pickup, putdown, stack and unstack.
    	ArrayList<ArrayList<HashMap<Term,Integer>>> encodingAllActionsHelper = new ArrayList<ArrayList<HashMap<Term,Integer>>>();
    	// We remember the name of the previous action, in order to avoid creating a new ArrayList for the next action
    	// if the two share the same name.
    	String previousOpName = "";
    	// Each time that this ArrayList is properly built, it represents an action with a specific name (eg. stack).
    	// These ArrayLists are the elements of the encodingAllActionsHelper ArrayList.
    	ArrayList<HashMap<Term,Integer>> encodingOneActionHelper = null;
    	// This variable will be equal to the total number of different ints that are used in order to
    	// encode all split actions of a same timestep.
    	// It is used in every step in order to give a different encoding number to a (split) action.
    	int dimacsNum = 0;
    	// The encodedActions ArrayList will be used in the following way:
    	// Each element is an ArrayList that corresponds to a grounded action for the first timestep.
    	// Those (inner) ArrayLists contain the dimacs numbers of that grounded action (for the first timestep).
    	// The encoding of actions of other timesteps is based on this ArrayList,
    	// so we don't need to generate any other ArrayLists.
    	ArrayList<ArrayList<Integer>> encodedActions = new ArrayList<ArrayList<Integer>>();

    	// There is a correspondence between the encodedTerms and encoded ArrayLists.
    	// The encodedTerms has the corresponding Terms of actions, and is consulted
    	// when we do the refactoring.
    	ArrayList<ArrayList<Term>> encodedActionsTerms = new ArrayList<ArrayList<Term>>();
    	
    	// This ArrayList contains "pointers" which are used to define the limits of
    	// actions having same name (this way we can "regroup" all instantiated actions).
    	ArrayList<Integer> groupActionsSameName = new ArrayList<Integer>();
    	
    	// The inner ArrayList that contains the dimacs numbers of a grounded action.
    	ArrayList<Integer> encoded = null;
    	// The inner ArrayList that contains the Terms of a grounded action.
    	ArrayList<Term> encodedTerms = null;

    	// We have to test for each grounded action, if there is the need to create an (encoded) ArrayList.
    	for (int i=0; i<ops_table_size; i++) {

    		Op currOp = ops_table.get(i);
    		int OpArity = currOp.getName().getArity();
    		// As we are proceeding to the construction of the hashmaps, in the same time,
    		// we will encode each action by associating it with an ArrayList of integers
    		//////////////////////////////////////
    		encoded = new ArrayList<Integer>(); 
    		encodedTerms = new ArrayList<Term>(); 
    		//////////////////////////////////////

    		// If we got an action with a different name than the previous,
    		// then we must create an ArrayList of HashMaps for this new action
    		if ( !currOp.getName().getPredicate().toString().equals(previousOpName) ) {
    			groupActionsSameName.add(i);
    			// remember for next iteration...
    			previousOpName = currOp.getName().getPredicate().toString();
    			// Create the ArrayList for this action.
    			encodingOneActionHelper = new ArrayList<HashMap<Term,Integer>>();
    			for (int j=0; j<OpArity; j++) {
    				encodingOneActionHelper.add(new HashMap<Term, Integer>());
    			}
    			// Continue the "construction" of the basic ArrayList (encodingAllActionsHelper).
    			encodingAllActionsHelper.add(encodingOneActionHelper);
    		}
    		// Now for each term of the currOp we have to find a corresponding number, with the help of 
    		// the corresponding HashMap, and (if it is a new one) we have to add this correspondence
    		// to the HashMap.
    		Iterator<Term> it = currOp.getName().iterator();
    		int index = 0;

    		while (it.hasNext()) {
    			// Check the proper HashMap. If the key has been used we can use its corresponding value.
    			// If there is no such key, we insert a new pair in the HashMap.
    			HashMap<Term, Integer> hmap = encodingOneActionHelper.get(index);
    			Term key = it.next();
    			if ( !hmap.containsKey(key) ) {
    				dimacsNum++;
    				hmap.put(key, dimacsNum);
    				////////////////////////
    				encoded.add(totalDimacsIdsFact + dimacsNum); 
    				encodedTerms.add(key);
    				////////////////////////	
    			} else {
    				/////////////////////////////
    				encoded.add(totalDimacsIdsFact + hmap.get(key));
    				encodedTerms.add(key);
    				/////////////////////////////	
    			}
    			index++;	
    		} // end-while
    		encodedActions.add(encoded);
    		encodedActionsTerms.add(encodedTerms);
    	} // end-for (each action)
    	// Add as last element of the list the total number of actions.
    	groupActionsSameName.add(encodedActions.size());
    	// We can now save the size of the ArrayList we constructed in order to use it later.
    	int encodedActionsSize = encodedActions.size();
    	
    	Fact currFact = null;
    	Iterator<Term> it = null;
    	Term term = null;
    	ArrayList<Integer> ans = null;
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			// When relating an action to a fluent, we need only include the parts of
    			// the action conjunct pertaining to the arguments that appear in the affected fluent.
    			// For the POSITIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getPositivePreconditon();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							// for example: arm_empty
    						// unstack_1_a AND unstack_2_b --> arm_empty
    						// We keep only the first part of the action (unstack_1_a --> arm_empty).
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							// We take the iterator over all the Terms of the currFact.
    							// For example, if currFact == (clear b), then
    							// the only term (on which we will iterate) is "b".
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact.
    					ans.add(findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" because it is a negative precondition).
    					ans.add(-findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the POSITIVE EFFECTS of actions...
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else { 
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact ("j+1" since we have an effect here).
    					ans.add(findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE EFFECTS of actions...
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" and "j+1" because it is a negative effect).
    					ans.add(-findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    		}
    	}
    	
    	// STAGE 4 (Explanatory Frame Axioms - Factored):
    	// For the POSITIVE EFFECTS OF ACTIONS, and also,
    	// for the NEGATIVE EFFECTS OF ACTIONS.
    	for (int i=0; i<facts_table_size; i++) {
    		// The actionsWithPosEff ArrayList contains (in the form of ArrayLists) all the actions
    		// which have the current fact to their POSITIVE EFFECTS.
    		// These actions are FACTORED (according to the fact)!
    		ArrayList<ArrayList<Integer>> actionsWithPosEff = new ArrayList<ArrayList<Integer>>();
    		// The actionsWithNegEff ArrayList contains (in the form of ArrayLists) all the actions
    		// which have the current fact to their NEGATIVE EFFECTS.
    		// These actions are FACTORED (according to the fact)!
    		ArrayList<ArrayList<Integer>> actionsWithNegEff = new ArrayList<ArrayList<Integer>>();
    		// The temporal ArrayList<Integer> will contain integers which represent parts of an action.
    		// Those integers represent the "factoring" of the action.
    		Iterator<Term> termIter;
    		// The boolean variable found, helps us decide whether we should keep an integer or not 
    		// when "factoring" an action.
    		boolean found = false;
    		// Fill the ArrayLists we just created with the proper data.
    		for (int j=0; j<ops_table_size; j++) {
    			// build the Arraylist for the positive effects.
    			if (ops_table.get(j).getPositiveEffect().get(i)) {
    				ArrayList<Integer> temporal = new ArrayList<Integer>();
    				termIter = facts_table.get(i).iterator();
    				if (!termIter.hasNext()) {
						// ex. armempty (blocksworld) is processed here.
						// We just take the first integer (part) of the action.
						temporal.add((Integer) encodedActions.get(j).get(0));
    				} else {
    					for (int k=0; k<encodedActions.get(j).size(); k++) {
    						found = false;
    						termIter = facts_table.get(i).iterator();
    						while (termIter.hasNext()) {
    							term = (Term)termIter.next();
    							if (term.equals(encodedActionsTerms.get(j).get(k))) {
    								found = true;
    							}
    						}
    						if (found) {
    							// we are forced to keep this part of the action.
    							temporal.add((Integer) encodedActions.get(j).get(k));
    						}
    					}
    				}
    				actionsWithPosEff.add(temporal);
    			}
    			// build the Arraylist for the negative effects.
    			if (ops_table.get(j).getNegativeEffect().get(i)) {
    				ArrayList<Integer> temporal = new ArrayList<Integer>();
    				termIter = facts_table.get(i).iterator();
    				if (!termIter.hasNext()) {
						// ex. armempty (blocksworld) is processed here.
						// We just take the first integer (part) of the action.
						temporal.add((Integer) encodedActions.get(j).get(0));
    				} else {
    					for (int k=0; k<encodedActions.get(j).size(); k++) {
    						found = false;
    						termIter = facts_table.get(i).iterator();
    						while (termIter.hasNext()) {
    							term = (Term)termIter.next();
    							if (term.equals(encodedActionsTerms.get(j).get(k))) {
    								found = true;
    							}
    						}
    						if (found) {
    							// we are forced to keep this part of the action.
    							temporal.add((Integer) encodedActions.get(j).get(k));
    						}
    					}
    				}
    				actionsWithNegEff.add(temporal);
    			}
    		}
    		// (end-for) end of construction of actionsWithPosEff and actionsWithNegEff (for the current fact).
    		
    		// The following "set of pointers" will help us find the result we search for.
    		// In order to encode the positive effects of actions we will have to obtain
    		// all the possible combinations of basic elements of the actionsWithPosEff ArrayList.
    		// The pointers[] variable will help accomplish this task.
    		// It contains actionsWithPosEff.size() "pointers",
    		// one for every action of the actionsWithPosEff ArrayList.
    		int[] pointers;
    		if (actionsWithPosEff.size()==0) {
    			pointers = null;
    		} else {
	    		pointers = new int[actionsWithPosEff.size()];
	    		for (int j=0; j<pointers.length; j++) {
	    			pointers[j] = 0;
	    		}
    		}
    		// If there is a "pointer" which is not "depleted", then
    		// the value of the respective boolean variable will have to be true; 
    		boolean posEffPointerNotDepleted;
    		boolean negEffPointerNotDepleted;
    		
    		// For each timestep... 
    		for (int t=0; t<num_steps_inPlan; t++) {
    			ArrayList<Integer> res = new ArrayList<Integer>();
    			
    			posEffPointerNotDepleted = true;
    			// A loop will give a different combination of the inner elements,
    			// which is a clause on the dimacs format.
    			while (posEffPointerNotDepleted) {
    				// The resulting piece of info needed for the solver.
    				// We don't compute the number of combinations, so we use an ArrayList.
    				// At the end, we will construct an int[] from this ArrayList.
    				res = new ArrayList<Integer>();
    				// Put the fact we are examining (POS - NEG: Because of negation...)
    				res.add(findDimacsIdFact(i, t));
    				res.add(-findDimacsIdFact(i, t+1));
    				// Put the current combination using the pointers[] variable.
    				if (pointers != null) {
    					for (int k=0; k<pointers.length; k++) {
    						res.add( (Integer)actionsWithPosEff.get(k).get(pointers[k]) + dimacsNum*t);
    					}
    					// Now we have to manipulate the pointers[] in order to be ready 
    					// to get the next combination in the next loop of the while,
    					// or to realise that there exist no more combinations. So...
    					// IF THE FIRST POINTER HAS REACHED ITS END...
    					if (pointers[0]==actionsWithPosEff.get(0).size()-1) {
    						// We reset the pointer to (0).
    						pointers[0] = 0;
    						// Now, work for the other pointers...
    						// If the following for loop doesn't change the value of the boolean variable,
    						// that means that all combinations have been computed
    						// (we are in the last combination).
    						posEffPointerNotDepleted = false;
    						for (int m=1; m<pointers.length && !posEffPointerNotDepleted; m++) {
    							// Reset to zero only pointers which form a "group"
    							// after the first pointer.
    							if (pointers[m] == actionsWithPosEff.get(m).size()-1) {
    								pointers[m] = 0;
    							}
    							else  { // if another pointer has not been depleted
    								// properly set its value.
    								pointers[m]++;
    								// We want to be able to continue the while loop.
    								posEffPointerNotDepleted = true;
    							}
    						}
    					} else { // We increase the number of the first pointer
    						pointers[0]++;
    					}
    				} else {
    					posEffPointerNotDepleted = false;
    				}
    				// Put the result we found into a clause and add it to the solver.
    				int[] mat = new int[res.size()];
    				for (int x=0; x<res.size(); x++) {
    					mat[x] = (Integer)res.get(x);
    				}
    				clause = new VecInt(mat);
        			solver.addClause(clause);
    			} //end-while
    			
    			// Then do the NEGATIVE EFFECTS OF ACTIONS.
    			if (actionsWithNegEff.size()==0) {
        			pointers = null;
        		} else {
    	    		pointers = new int[actionsWithNegEff.size()];
    	    		for (int j=0; j<pointers.length; j++) {
    	    			pointers[j] = 0;
    	    		}
        		}
    			negEffPointerNotDepleted = true;
    			while (negEffPointerNotDepleted) {
    				res = new ArrayList<Integer>();
    				// Put the fact we are examining (NEG - POS: Because of negation...)
    				res.add(-findDimacsIdFact(i, t));
    				res.add(findDimacsIdFact(i, t+1));
    				if (pointers != null) {
    					// Put the current combination using the pointers[] variable.
    					for (int k=0; k<pointers.length; k++) {
    						res.add((Integer)actionsWithNegEff.get(k).get(pointers[k]) + dimacsNum*t);
    					}
    					if (pointers[0]==actionsWithNegEff.get(0).size()-1) {
    						// We reset the pointer to (0).
    						pointers[0] = 0;
    						// Now, work for the other pointers...
    						negEffPointerNotDepleted = false;
    						for (int m=1; m<pointers.length && !negEffPointerNotDepleted; m++) {
    							// Reset to zero only pointers which form a "group"
    							// after the first pointer.
    							if (pointers[m] == actionsWithNegEff.get(m).size()-1) {
    								pointers[m] = 0;
    							}
    							else  { // if another pointer has not been depleted
    								// properly set its value.
    								pointers[m]++;
    								// We want to be able to continue the while loop.
    								negEffPointerNotDepleted = true;
    							}
    						}
    					} else { // We increase the number of the first pointer
    						pointers[0]++;
    					}
    				} else {
    					negEffPointerNotDepleted = false;
    				}
    				// Put the result we found into a clause and add it to the solver.
    				int[] mat= new int[res.size()];
    				for (int x=0; x<res.size(); x++) {
    					mat[x] = (Integer)res.get(x);
    				}
    				clause = new VecInt(mat);
        			solver.addClause(clause);
    			} //end-while
    		}// end-for (each timestep)
    	}// end-for (each fact)
    	
    	// STAGE 5 (Complete Exclusion Axioms - Not Factored):
    	for (int t=0; t<num_steps_inPlan; t++) { // do for every timestep
    		// No two actions can happen at the same time.
    		for (int i=0; i<encodedActionsSize; i++) {
    			for (int j=i+1; j<encodedActionsSize; j++) {

    				ArrayList<Integer> a = encodedActions.get(i);
    				ArrayList<Integer> b = encodedActions.get(j);

    				int[] mat = new int[a.size() + b.size()];
    				// Fill half the data of a clause
    				for (int l=0; l<a.size(); l++) {
    					mat[l] = -((Integer)a.get(l) + dimacsNum*t);
    				}
    				// Fill the other half of the clause
    				for (int l=0; l<b.size(); l++) {
    					mat[a.size()+l] = -((Integer)b.get(l)+ dimacsNum*t);
    				}
    				clause = new VecInt(mat);
    				solver.addClause(clause);
    			}
    		}
    	}
    	
    	// STAGE 6 (No-Partial Axioms - Simple Operator Splitting)
    	// These axioms state that whenever any part of an operator is instantiated,
    	// so is the rest (some complete instantiation of the action is true).
    	// These axioms have to be added because we use factoring.
    	for (int i=0; i<num_steps_inPlan; i++) {
    		for (int j=0; j<groupActionsSameName.size()-1; j++) {
    			// The a and b integers define the location of a group of actions having the same name.
    			int a = groupActionsSameName.get(j);
    			int b = groupActionsSameName.get(j+1);
    			int actionParams = encodedActions.get(a).size();
    			if (actionParams==1) {
    				// no action needed (no partial action danger).
    			} else {
    				// Here we have to take care of every part of the action,
    				// beginning with Arg1, then Arg2 etc.
    				for (int k=0; k<actionParams; k++) {
    					// First, we construct the ArrayList with all the nums we will 
    					// make rules for in this step (step: the current argument of the current action-name).
    					// ex. for: stack_1 (blocksworld), we have: stack_1_a , stack_1_b .
    					ArrayList<Integer> working = new ArrayList<Integer>();
    					for (int x=a; x<b; x++) {
    						if ( !working.contains(encodedActions.get(x).get(k))) {
    							working.add( (Integer) encodedActions.get(x).get(k)); 
    						}
    					}
    					// For each num in the working ArrayList...
    					int currNum;
    					for (int l=0; l<working.size(); l++) {
    						currNum = (Integer) working.get(l);
    						for (int n=0; n<actionParams; n++) {
    							// For each other argument (different than the current one which is 'k') 
    							// of the same action-name, we have to make a rule...
    							if (n!=k) {
	    							// This ArrayList stocks the "rule" we will make for the currNum.
	    							ArrayList<Integer> rule = new ArrayList<Integer>();
	    							rule.add(-(currNum + dimacsNum*i));
	    							// Check all actions in the group (with the same name)...
	    							for (int m=a; m<b; m++) {
	    								if ( (Integer) encodedActions.get(m).get(k)==currNum) {
	    									if ( !rule.contains(encodedActions.get(m).get(n) + dimacsNum*i )) {
	    										rule.add( (Integer)encodedActions.get(m).get(n) + dimacsNum*i  );
	    									}
	    								}
	    							}
	    							int[] mat= new int[rule.size()];
	    							for (int x=0; x<rule.size(); x++) {
	    								mat[x] = (Integer)rule.get(x);
	    							}
	    							clause = new VecInt(mat);
	    							solver.addClause(clause);
    							}
    						}
    					}		
    				}
    			}
    		}	
    	}
    	
    	IProblem problem = solver;
    	// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
		int[] mysolution = problem.findModel();
		
		if (mysolution != null) {
			System.out.println("*** THE PROBLEM IS SATISFIABLE! ***");
			System.out.println();
			System.out.println("The proposed solution is the following:");
			System.out.println();
			
			// We translate the solution into an understandable form of a plan.
			this.translateSolutionOperatorSplitting(mysolution, dimacsNum, encodedActions);
			
        } else {
            System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
        }
		
    	return;
    }
    
    /**
     * Finds and displays a solution to our problem, provided that there exists one.
     * Otherwise, it declares the problem unsatisfiable.
     * The sat4j library is used to find the solution.
     * Encodes the actions of the problem using the method of Simple-Operator-Splitting.
     * It also uses the Classical Frame Axioms and the At-Least-One Axioms.
     * It implements the technique of factoring, in order to avoid combinatorial explosion when
     * trying to convert clauses into CNF.
     * @throws ContradictionException, TimeoutException 
     */
    public void solveSimpleOpSplittClassFrameFactoring() throws ContradictionException, TimeoutException {

    	final int MAXVAR = 1000000;
    	final int NBCLAUSES = 500000;

    	ISolver solver = SolverFactory.newDefault();
    	// prepare the solver to accept MAXVAR variables. MANDATORY
    	solver.newVar(MAXVAR);
    	// not mandatory for SAT solving. MANDATORY for MAXSAT solving
    	solver.setExpectedNumberOfClauses(NBCLAUSES);
    	// Feed the solver using Dimacs format, using arrays of int
    	// (best option to avoid dependencies on SAT4J IVecInt)

    	/**
    	 * We will use this variable in order to build all necessary clauses (one by one).
    	 */
    	VecInt clause;

    	// STAGE 1 (Initial State):
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...

    			if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
    				clause = new VecInt(new int[]{findDimacsIdFact(i, 0)});
    				solver.addClause(clause);
    				isInit = true ;
    				continue;
    			} 
    		}
    		if (!isInit){
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, 0)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}

    	// Stage 3 (Actions Encoding - SIMPLE OPERATOR SPLITTING - Factored):
    	// The basic ArrayList (encodingAllActionsHelper) which contains an ArrayList for each action with a different name.
    	// For example, in the blocksworld, we have the basic ArrayList (encodingAllActionsHelper) that contains 4 ArrayLists,
    	// which correspond to the actions: pickup, putdown, stack and unstack.
    	ArrayList<ArrayList<HashMap<Term,Integer>>> encodingAllActionsHelper = new ArrayList<ArrayList<HashMap<Term,Integer>>>();
    	// We remember the name of the previous action, in order to avoid creating a new ArrayList for the next action
    	// if the two share the same name.
    	String previousOpName = "";
    	// Each time that this ArrayList is properly built, it represents an action with a specific name (eg. stack).
    	// These ArrayLists are the elements of the encodingAllActionsHelper ArrayList.
    	ArrayList<HashMap<Term,Integer>> encodingOneActionHelper = null;
    	// This variable will be equal to the total number of different ints that are used in order to
    	// encode all split actions of a same timestep.
    	// It is used in every step in order to give a different encoding number to a (split) action.
    	int dimacsNum = 0;
    	// The encodedActions ArrayList will be used in the following way:
    	// Each element is an ArrayList that corresponds to a grounded action for the first timestep.
    	// Those (inner) ArrayLists contain the dimacs numbers of that grounded action (for the first timestep).
    	// The encoding of actions of other timesteps is based on this ArrayList,
    	// so we don't need to generate any other ArrayLists.
    	ArrayList<ArrayList<Integer>> encodedActions = new ArrayList<ArrayList<Integer>>();

    	// There is a correspondence between the encodedTerms and encoded ArrayLists.
    	// The encodedTerms has the corresponding Terms of actions, and is consulted
    	// when we do the refactoring.
    	ArrayList<ArrayList<Term>> encodedActionsTerms = new ArrayList<ArrayList<Term>>();
    	
    	// This ArrayList contains "pointers" which are used to define the limits of
    	// actions having same name (this way we can "regroup" all instantiated actions).
    	ArrayList<Integer> groupActionsSameName = new ArrayList<Integer>();
    	
    	// The inner ArrayList that contains the dimacs numbers of a grounded action.
    	ArrayList<Integer> encoded = null;
    	// The inner ArrayList that contains the Terms of a grounded action.
    	ArrayList<Term> encodedTerms = null;
    	/////////////////////////////////////////////////////////////////////////////////////////////////////////
    	// The ArrayList that contains all the numbers we use to encode all actions (for the first timestep).
    	ArrayList<Integer> allEncodingNumbers = new ArrayList<Integer>();
    	/////////////////////////////////////////////////////////////////////////////////////////////////////////

    	// We have to test for each grounded action, if there is the need to create an (encoded) ArrayList.
    	for (int i=0; i<ops_table_size; i++) {

    		Op currOp = ops_table.get(i);
    		int OpArity = currOp.getName().getArity();
    		// As we are proceeding to the construction of the hashmaps, in the same time,
    		// we will encode each action by associating it with an ArrayList of integers
    		//////////////////////////////////////
    		encoded = new ArrayList<Integer>(); 
    		encodedTerms = new ArrayList<Term>(); 
    		//////////////////////////////////////

    		// If we got an action with a different name than the previous,
    		// then we must create an ArrayList of HashMaps for this new action
    		if ( !currOp.getName().getPredicate().toString().equals(previousOpName) ) {
    			groupActionsSameName.add(i);
    			// remember for next iteration...
    			previousOpName = currOp.getName().getPredicate().toString();
    			// Create the ArrayList for this action.
    			encodingOneActionHelper = new ArrayList<HashMap<Term,Integer>>();
    			for (int j=0; j<OpArity; j++) {
    				encodingOneActionHelper.add(new HashMap<Term, Integer>());
    			}
    			// Continue the "construction" of the basic ArrayList (encodingAllActionsHelper).
    			encodingAllActionsHelper.add(encodingOneActionHelper);
    		}
    		// Now for each term of the currOp we have to find a corresponding number, with the help of 
    		// the corresponding HashMap, and (if it is a new one) we have to add this correspondence
    		// to the HashMap.
    		Iterator<Term> it = currOp.getName().iterator();
    		int index = 0;

    		while (it.hasNext()) {
    			// Check the proper HashMap. If the key has been used we can use its corresponding value.
    			// If there is no such key, we insert a new pair in the HashMap.
    			HashMap<Term, Integer> hmap = encodingOneActionHelper.get(index);
    			Term key = (Term)it.next();
    			if ( !hmap.containsKey(key) ) {
    				dimacsNum++;
    				hmap.put(key, dimacsNum);
    				////////////////////////
    				encoded.add(totalDimacsIdsFact + dimacsNum);
    				encodedTerms.add(key);
    				allEncodingNumbers.add(totalDimacsIdsFact + dimacsNum);
    				////////////////////////	
    			} else {
    				/////////////////////////////
    				encoded.add(totalDimacsIdsFact + hmap.get(key));
    				encodedTerms.add(key);
    				/////////////////////////////	
    			}
    			index++;	
    		} // end-while
    		encodedActions.add(encoded);
    		encodedActionsTerms.add(encodedTerms);
    	} // end-for (each action)
    	// Add as last element of the list the total number of actions.
    	groupActionsSameName.add(encodedActions.size());
    	// We can now save the size of the ArrayList we constructed in order to use it later.
    	
    	Fact currFact = null;
    	Iterator<Term> it = null;
    	Term term = null;
    	ArrayList<Integer> ans = null;
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			// When relating an action to a fluent, we need only include the parts of
    			// the action conjunct pertaining to the arguments that appear in the affected fluent.
    			// For the POSITIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getPositivePreconditon();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							// for example: arm_empty
    						// unstack_1_a AND unstack_2_b --> arm_empty
    						// We keep only the first part of the action (unstack_1_a --> arm_empty).
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							// We take the iterator over all the Terms of the currFact.
    							// For example, if currFact == (clear b), then
    							// the only term (on which we will iterate) is "b".
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact
    					ans.add(findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" because it is a negative precondition).
    					ans.add(-findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the POSITIVE EFFECTS of actions...
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else { 
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact ("j+1" since we have an effect here).
    					ans.add(findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE EFFECTS of actions...
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						for (int l=0; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" and "j+1" because it is a negative effect).
    					ans.add(-findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    		}
    	}
    	
    	// STAGE 4 (Classical Frame Axioms - Not Factored):
    	// If fluentF is not an effect of actionA, then:
    	// fluentF_i AND actionA_i --> fluentF_i+1  ======>  (NOT fluentF_i) OR (NOT actionA_i) OR fluentF_i+1
    	// (NOT fluentF_i) AND actionA_i --> (NOT fluentF_i+1)  ======>  fluentF_i OR (NOT actionA_i) OR (NOT fluentF_i+1)
    	// We will create clauses for each action which will impose that fluents not belonging
    	// to the effects of the action must remain the same after the action's execution.
    	// The difference to the Regular Encoding is that now all actions are "splitted" actions.
    	for (int i=0; i<ops_table_size; i++) {
    		Op curr = ops_table.get(i);
    		BitSet posEff = null;
			BitSet negEff = null;
 			// find the action's effects
			posEff = curr.getPositiveEffect();
			negEff = curr.getNegativeEffect();
			for (int j=0; j<facts_table_size; j++) {
				// If the fact is neither in the current action's positive effects,
				// nor in its negative effects, we should build a clause for the 
				// classical frame axiom. 
				if ( !posEff.get(j) && !negEff.get(j)) {
					for (int k=0; k<num_steps_inPlan; k++) {
						ArrayList<Integer> temp = new ArrayList<Integer>();
						temp.add(-findDimacsIdFact(j, k));
						for (int l=0; l<encodedActions.get(i).size(); l++) {
							temp.add( -( (Integer)encodedActions.get(i).get(l) + dimacsNum*k) );
						}
						temp.add(findDimacsIdFact(j, k+1));
						int[] mat = new int[temp.size()];
						for (int l=0; l<mat.length; l++) {
							mat[l] = temp.get(l);
						}
						clause = new VecInt(mat);
						solver.addClause(clause);
						mat[0] = -mat[0];
						mat[mat.length-1] = -mat[mat.length-1];
						clause = new VecInt(mat);
						solver.addClause(clause);
					}
				}
    		}
    	}
    	
    	// STAGE 5 (At-Least-One Axioms - Factored)
    	// Factoring these axioms is essential in order to have a method that runs in acceptable time (at least in easy cases).
    	for (int i=0; i<num_steps_inPlan; i++) {
    		int[] mat = new int[encodedActions.size()];
    		for (int j=0; j<mat.length; j++) {
    			// Always take the first integer of each action.
    			mat[j] = (Integer) encodedActions.get(j).get(0) + dimacsNum * i;	
    		}
    		clause = new VecInt(mat);
			solver.addClause(clause);
    	}
    	
    	// STAGE 6 (No-Partial Axioms - Simple Operator Splitting)
    	// These axioms state that whenever any part of an operator is instantiated,
    	// so is the rest (some complete instantiation of the action is true).
    	// These axioms have to be added because we use factoring.
    	for (int i=0; i<num_steps_inPlan; i++) {
    		for (int j=0; j<groupActionsSameName.size()-1; j++) {
    			// The a and b integers define the location of a group of actions having the same name.
    			int a = groupActionsSameName.get(j);
    			int b = groupActionsSameName.get(j+1);
    			int actionParams = encodedActions.get(a).size();
    			if (actionParams==1) {
    				// no action needed (no partial action danger).
    			} else {
    				// Here we have to take care of every part of the action,
    				// beginning with Arg1, then Arg2 etc.
    				for (int k=0; k<actionParams; k++) {
    					// First, we construct the ArrayList with all the nums we will 
    					// make rules for in this step (step: the current argument of the current action-name).
    					// ex. for: stack_1 (blocksworld), we have: stack_1_a , stack_1_b .
    					ArrayList<Integer> working = new ArrayList<Integer>();
    					for (int x=a; x<b; x++) {
    						if ( !working.contains(encodedActions.get(x).get(k))) {
    							working.add( (Integer) encodedActions.get(x).get(k)); 
    						}
    					}
    					// For each num in the working ArrayList...
    					int currNum;
    					for (int l=0; l<working.size(); l++) {
    						currNum = (Integer) working.get(l);
    						for (int n=0; n<actionParams; n++) {
    							// For each other argument (different than the current one which is 'k') 
    							// of the same action-name, we have to make a rule...
    							if (n!=k) {
	    							// This ArrayList stocks the "rule" we will make for the currNum.
	    							ArrayList<Integer> rule = new ArrayList<Integer>();
	    							rule.add(-(currNum + dimacsNum*i));
	    							// Check all actions in the group (with the same name)...
	    							for (int m=a; m<b; m++) {
	    								if ( (Integer) encodedActions.get(m).get(k)==currNum) {
	    									if ( !rule.contains(encodedActions.get(m).get(n) + dimacsNum*i )) {
	    										rule.add( (Integer)encodedActions.get(m).get(n) + dimacsNum*i  );
	    									}
	    								}
	    							}
	    							int[] mat= new int[rule.size()];
	    							for (int x=0; x<rule.size(); x++) {
	    								mat[x] = (Integer)rule.get(x);
	    							}
	    							clause = new VecInt(mat);
	    							solver.addClause(clause);
    							}
    						}
    					}		
    				}
    			}
    		}	
    	}
    	
    	IProblem problem = solver;
    	// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
		int[] mysolution = problem.findModel();
		
		if (mysolution != null) {
			System.out.println("*** THE PROBLEM IS SATISFIABLE! ***");
			System.out.println();
			System.out.println("The proposed solution is the following:");
			System.out.println();
			
			// We translate the solution into an understandable form of a plan.
			this.translateSolutionOperatorSplitting(mysolution, dimacsNum, encodedActions);
			
        } else {
            System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
        }
		
    	return;
    }
    
    /**
     * Finds and displays a solution to our problem, provided that there exists one.
     * Otherwise, it declares the problem unsatisfiable.
     * The sat4j library is used to find the solution.
     * Encodes the actions of the problem using the method of Overloaded-Operator-Splitting.
     * It also uses the Explanatory Frame Axioms and the Complete Exclusion Axioms.
     * It implements the technique of factoring, in order to avoid combinatorial explosion,
     * when trying to convert clauses into CNF.
     * @throws ContradictionException, TimeoutException 
     */
    public void solveOverloadOpSplittExplanFrameFactoring() throws ContradictionException, TimeoutException {

    	final int MAXVAR = 1000000;
    	final int NBCLAUSES = 500000;

    	ISolver solver = SolverFactory.newDefault();
    	// prepare the solver to accept MAXVAR variables. MANDATORY
    	solver.newVar(MAXVAR);
    	// not mandatory for SAT solving. MANDATORY for MAXSAT solving
    	solver.setExpectedNumberOfClauses(NBCLAUSES);
    	// Feed the solver using Dimacs format, using arrays of int
    	// (best option to avoid dependencies on SAT4J IVecInt)

    	/**
    	 * We will use this variable in order to build all necessary clauses (one by one).
    	 */
    	VecInt clause;

    	// STAGE 1 (Initial State):
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...
        		if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
        			clause = new VecInt(new int[]{findDimacsIdFact(i, 0)});
        			solver.addClause(clause);
        			isInit = true ;
        			continue;
        		} 
    		}
    		if (!isInit){
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, 0)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// Stage 3 (Actions Encoding - OVERLOADED OPERATOR SPLITTING - Factored):
    	// We have to create one HashMap to encode every different action name with a different number.
    	HashMap<String, Integer> actionNamesHelper = new HashMap<String, Integer>();
    	// We have to create a matrix of HashMaps where each HashMap will be referring to the 'n' argument
    	// of the actions. When we will instantiate the matrix, its length will be equal to the number of arguments of the action
    	// which has the maximum number of arguments.
    	HashMap<Term, Integer>[] actionDataHelper;
    	// The encodedActions ArrayList will be used in the following way:
    	// Each element is an ArrayList that corresponds to a grounded action for the first timestep.
    	// Those (inner) ArrayLists contain the dimacs numbers of that grounded action (for the first timestep).
    	// The encoding of actions of other timesteps is based on this ArrayList,
    	// so we don't need to generate any other ArrayLists.
    	ArrayList<ArrayList<Integer>> encodedActions = new ArrayList<ArrayList<Integer>>();
    	// There is a correspondence between the encodedTerms and encoded ArrayLists.
    	// The encodedTerms has the corresponding Terms of actions, and is consulted
    	// when we do the refactoring.
    	ArrayList<ArrayList<Term>> encodedActionsTerms = new ArrayList<ArrayList<Term>>();
    	
    	// This ArrayList contains "pointers" which are used to define the limits of
    	// actions having the same name (this way we can "regroup" all instantiated actions).
    	ArrayList<Integer> groupActionsSameName = new ArrayList<Integer>();
    	
    	// The inner ArrayList that contains the dimacs numbers of a grounded action.
    	ArrayList<Integer> encoded = null;
    	// The inner ArrayList that contains the Terms of a grounded action.
    	ArrayList<Term> encodedTerms = null;
    	// This variable will be equal to the total number of different ints that are used in order to
    	// encode all split actions of a same timestep.
    	// It is used in every step in order to give a different encoding number to a (splitted) action.
    	int dimacsNum = 0;
    	// The number of arguments of the action which has the most arguments.
    	int maxArguments = 0;

    	// Fill the actionNamesHelper HashMap. 
    	String previousOpName = "";
    	// Helps us construct the groupActionsSameName ArrayList.
    	int pointerOfActionNames = 0;
    	for (int i=0; i<ops_table_size; i++) {
    		String currOpName = this.ops_table.get(i).getName().getPredicate();
    		if ( !currOpName.equals(previousOpName) ) {
    			// Constructing the groupActionsSameName ArrayList...
    			groupActionsSameName.add(pointerOfActionNames);
    			// We will provide a number for this action name.
    			dimacsNum++;
    			actionNamesHelper.put(currOpName, this.totalDimacsIdsFact + dimacsNum);
    			if (this.ops_table.get(i).getName().getArity() > maxArguments) {
    				// Update the maxArguments variable.
    				maxArguments = this.ops_table.get(i).getName().getArity();
    			}
    		}
    		previousOpName = currOpName;
    		pointerOfActionNames++;
    	}
    	// Add the last element to the groupActionsSameName ArrayList. It is now ready.
    	groupActionsSameName.add(ops_table_size);
    	
    	// Create the HashMaps of the actionDataHelper ArrayList.
    	actionDataHelper = new HashMap[maxArguments];
    	for (int i=0; i<maxArguments; i++) {	
    		actionDataHelper[i] = new HashMap<Term, Integer>();
    	}
    	// Fill the HashMaps and, at the same time, construct 
    	// the encodedActions and encodedActionsTerms ArrayLists.
    	for (int i=0; i<this.ops_table_size; i++) {
    		Op currAction = ops_table.get(i);
    		// We have to encode the current action.
    		encoded = new ArrayList<Integer>();
    		encodedTerms = new ArrayList<Term>();
    		// The first element of encoded is the number corresponding to the action's name.
    		encoded.add(actionNamesHelper.get(currAction.getName().getPredicate()));
    		// There exists no corresponding Term for the action's first part (the name).
    		encodedTerms.add(null);
    		// For every argument of the currAction we must check if we should put a new value to the corresponding HashMap,
    		// or if we just use a value that we already have there.
    		Iterator<Term> it = currAction.getName().iterator();
    		int ptr = 0;
    		while (it.hasNext()) {
    			Term currTerm = it.next();
    			if ( !actionDataHelper[ptr].containsKey(currTerm) ) {
    				// It's the first time we come across this term for this argument.
    				dimacsNum++;
    				actionDataHelper[ptr].put(currTerm, this.totalDimacsIdsFact + dimacsNum);
    				encoded.add(this.totalDimacsIdsFact + dimacsNum);
    				encodedTerms.add(currTerm);
    			} else {
    				// We have already come across this term for this argument.
    				encoded.add(actionDataHelper[ptr].get(currTerm));
    				encodedTerms.add(currTerm);
    			}
    			ptr++;
    		}
    		encodedActions.add(encoded);
    		encodedActionsTerms.add(encodedTerms);
    	}
    	
    	Fact currFact = null;
    	Iterator<Term> it = null;
    	Term term = null;
    	ArrayList<Integer> ans = null;
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			// When relating an action to a fluent, we only need to include the parts of
    			// the action that have arguments appearing in the affected fluent,
    			// as well as the name of the action.
    			// For the POSITIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getPositivePreconditon();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							// for example: arm_empty
    						// (pickup) AND (Arg_1_a) --> arm_empty
    						// We factor the action by keeping only the name of the action (pickup).
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						// Also now (in overloaded-op-split) we have to keep the action's name...
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						// As well as (beginning from l=1)...
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							// We take the iterator over all the Terms of the currFact.
    							// For example, if currFact == (clear b), then
    							// the only term (on which we will iterate) is "b".
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact
    					ans.add(findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" because it is a negative precondition).
    					ans.add(-findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the POSITIVE EFFECTS of actions...
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else { 
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact ("j+1" since we have an effect here).
    					ans.add(findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE EFFECTS of actions...
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" and "j+1" because it is a negative effect).
    					ans.add(-findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    		}
    	}
    	
    	// STAGE 4 (Explanatory Frame Axioms - Factored):
    	// For the POSITIVE EFFECTS OF ACTIONS, and also,
    	// for the NEGATIVE EFFECTS OF ACTIONS.
    	for (int i=0; i<facts_table_size; i++) {
    		// The actionsWithPosEff ArrayList contains (in the form of ArrayLists) all the actions
    		// which have the current fact to their POSITIVE EFFECTS.
    		// These actions are FACTORED (according to the fact)!
    		ArrayList<ArrayList<Integer>> actionsWithPosEff = new ArrayList<ArrayList<Integer>>();
    		// The actionsWithNegEff ArrayList contains (in the form of ArrayLists) all the actions
    		// which have the current fact to their NEGATIVE EFFECTS.
    		// These actions are FACTORED (according to the fact)!
    		ArrayList<ArrayList<Integer>> actionsWithNegEff = new ArrayList<ArrayList<Integer>>();
    		//
    		Iterator<Term> termIter;
    		// The boolean variable found, helps us decide whether we should keep an integer or not 
    		// when "factoring" an action.
    		boolean found = false;
    		// Fill the ArrayLists we just created with the proper data.
    		for (int j=0; j<ops_table_size; j++) {
    			// build the Arraylist for the positive effects.
    			if (ops_table.get(j).getPositiveEffect().get(i)) {
    				// The temporal ArrayList<Integer> will contain integers which represent parts of an action.
    	    		// Those integers represent the "factoring" of the action.
    				ArrayList<Integer> temporal = new ArrayList<Integer>();
    				termIter = facts_table.get(i).iterator();
    				if (!termIter.hasNext()) {
						// ex. arm-empty (blocksworld) is processed here.
						// We just take the first integer (part) of the action (the action's name).
						temporal.add((Integer) encodedActions.get(j).get(0));
    				} else {
    					// First take the action's name, then loop (for).
    					temporal.add((Integer) encodedActions.get(j).get(0));
    					for (int k=1; k<encodedActions.get(j).size(); k++) {
    						found = false;
    						termIter = facts_table.get(i).iterator();
    						while (termIter.hasNext()) {
    							term = (Term)termIter.next();
    							if (term.equals(encodedActionsTerms.get(j).get(k))) {
    								found = true;
    							}
    						}
    						if (found) {
    							// we are forced to keep this part of the action.
    							temporal.add((Integer) encodedActions.get(j).get(k));
    						}
    					}
    				}
    				actionsWithPosEff.add(temporal);
    			}
    			// build the Arraylist for the negative effects.
    			if (ops_table.get(j).getNegativeEffect().get(i)) {
    				ArrayList<Integer> temporal = new ArrayList<Integer>();
    				termIter = facts_table.get(i).iterator();
    				if (!termIter.hasNext()) {
						// ex. armempty (blocksworld) is processed here.
						// We just take the first integer (part) of the action (the action's name).
						temporal.add((Integer) encodedActions.get(j).get(0));
    				} else {
    					// First take the action's name, then loop (for).
    					temporal.add((Integer) encodedActions.get(j).get(0));
    					for (int k=1; k<encodedActions.get(j).size(); k++) {
    						found = false;
    						termIter = facts_table.get(i).iterator();
    						while (termIter.hasNext()) {
    							term = (Term)termIter.next();
    							if (term.equals(encodedActionsTerms.get(j).get(k))) {
    								found = true;
    							}
    						}
    						if (found) {
    							// we are forced to keep this part of the action.
    							temporal.add((Integer) encodedActions.get(j).get(k));
    						}
    					}
    				}
    				actionsWithNegEff.add(temporal);
    			}
    		}
    		// (end-for) end of construction of actionsWithPosEff and actionsWithNegEff (for the current fact).
    		
    		// The following "set of pointers" will help us find the result we search for.
    		// In order to encode the positive effects of actions we will have to obtain
    		// all the possible combinations of basic elements of the actionsWithPosEff ArrayList.
    		// The pointers[] variable will help accomplish this task.
    		// It contains actionsWithPosEff.size() "pointers",
    		// one for every action of the actionsWithPosEff ArrayList.
    		int[] pointers;
    		if (actionsWithPosEff.size()==0) {
    			pointers = null;
    		} else {
	    		pointers = new int[actionsWithPosEff.size()];
	    		for (int j=0; j<pointers.length; j++) {
	    			pointers[j] = 0;
	    		}
    		}
    		// If there is a "pointer" which is not "depleted", then
    		// the value of the respective boolean variable will have to be true; 
    		boolean posEffPointerNotDepleted;
    		boolean negEffPointerNotDepleted;
    		
    		// For each timestep... 
    		for (int t=0; t<num_steps_inPlan; t++) {
    			ArrayList<Integer> res = new ArrayList<Integer>();
    			
    			posEffPointerNotDepleted = true;
    			// A loop will give a different combination of the inner elements,
    			// which is a clause on the dimacs format.
    			while (posEffPointerNotDepleted) {
    				// The resulting piece of info needed for the solver.
    				// We don't compute the number of combinations, so we use an ArrayList.
    				// At the end, we will construct an int[] from this ArrayList.
    				res = new ArrayList<Integer>();
    				// Put the fact we are examining (POS - NEG: Because of negation...)
    				res.add(findDimacsIdFact(i, t));
    				res.add(-findDimacsIdFact(i, t+1));
    				// Put the current combination using the pointers[] variable.
    				if (pointers != null) {
    					for (int k=0; k<pointers.length; k++) {
    						res.add( (Integer)actionsWithPosEff.get(k).get(pointers[k]) + dimacsNum*t);
    					}
    					// Now we have to manipulate the pointers[] in order to be ready 
    					// to get the next combination in the next loop of the while,
    					// or to realise that there exist no more combinations. So...
    					// IF THE FIRST POINTER HAS REACHED ITS END...
    					if (pointers[0]==actionsWithPosEff.get(0).size()-1) {
    						// We reset the pointer to (0).
    						pointers[0] = 0;
    						// Now, work for the other pointers...
    						// If the following for loop doesn't change the value of the boolean variable,
    						// that means that all combinations have been computed
    						// (we are in the last combination).
    						posEffPointerNotDepleted = false;
    						for (int m=1; m<pointers.length && !posEffPointerNotDepleted; m++) {
    							// Reset to zero only pointers which form a "group"
    							// after the first pointer.
    							if (pointers[m] == actionsWithPosEff.get(m).size()-1) {
    								pointers[m] = 0;
    							}
    							else  { // if another pointer has not been depleted
    								// properly set its value.
    								pointers[m]++;
    								// We want to be able to continue the while loop.
    								posEffPointerNotDepleted = true;
    							}
    						}
    					} else { // We increase the number of the first pointer
    						pointers[0]++;
    					}
    				} else {
    					posEffPointerNotDepleted = false;
    				}
    				// Put the result we found into a clause and add it to the solver.
    				int[] mat = new int[res.size()];
    				for (int x=0; x<res.size(); x++) {
    					mat[x] = (Integer)res.get(x);
    				}
    				clause = new VecInt(mat);
        			solver.addClause(clause);
    			} //end-while
    			
    			// Then do the NEGATIVE EFFECTS OF ACTIONS.
    			if (actionsWithNegEff.size()==0) {
        			pointers = null;
        		} else {
    	    		pointers = new int[actionsWithNegEff.size()];
    	    		for (int j=0; j<pointers.length; j++) {
    	    			pointers[j] = 0;
    	    		}
        		}
    			negEffPointerNotDepleted = true;
    			while (negEffPointerNotDepleted) {
    				res = new ArrayList<Integer>();
    				// Put the fact we are examining (NEG - POS: Because of negation...)
    				res.add(-findDimacsIdFact(i, t));
    				res.add(findDimacsIdFact(i, t+1));
    				if (pointers != null) {
    					// Put the current combination using the pointers[] variable.
    					for (int k=0; k<pointers.length; k++) {
    						res.add((Integer)actionsWithNegEff.get(k).get(pointers[k]) + dimacsNum*t);
    					}
    					if (pointers[0]==actionsWithNegEff.get(0).size()-1) {
    						// We reset the pointer to (0).
    						pointers[0] = 0;
    						// Now, work for the other pointers...
    						negEffPointerNotDepleted = false;
    						for (int m=1; m<pointers.length && !negEffPointerNotDepleted; m++) {
    							// Reset to zero only pointers which form a "group"
    							// after the first pointer.
    							if (pointers[m] == actionsWithNegEff.get(m).size()-1) {
    								pointers[m] = 0;
    							}
    							else  { // if another pointer has not been depleted
    								// properly set its value.
    								pointers[m]++;
    								// We want to be able to continue the while loop.
    								negEffPointerNotDepleted = true;
    							}
    						}
    					} else { // We increase the number of the first pointer
    						pointers[0]++;
    					}
    				} else {
    					negEffPointerNotDepleted = false;
    				}
    				// Put the result we found into a clause and add it to the solver.
    				int[] mat= new int[res.size()];
    				for (int x=0; x<res.size(); x++) {
    					mat[x] = (Integer)res.get(x);
    				}
    				clause = new VecInt(mat);
        			solver.addClause(clause);
    			} //end-while
    		}// end-for (each timestep)
    	}// end-for (each fact)
    	
    	// STAGE 5 (Complete Exclusion Axioms - Not Factored):
    	for (int t=0; t<num_steps_inPlan; t++) { // do for every timestep
    		// No two actions can happen at the same time.
    		for (int i=0; i<encodedActions.size(); i++) {
    			for (int j=i+1; j<encodedActions.size(); j++) {

    				ArrayList<Integer> a = encodedActions.get(i);
    				ArrayList<Integer> b = encodedActions.get(j);

    				int[] mat = new int[a.size() + b.size()];
    				// Fill half the data of a clause
    				for (int l=0; l<a.size(); l++) {
    					mat[l] = -((Integer)a.get(l) + dimacsNum*t);
    				}
    				// Fill the other half of the clause
    				for (int l=0; l<b.size(); l++) {
    					mat[a.size()+l] = -((Integer)b.get(l) + dimacsNum*t);
    				}
    				clause = new VecInt(mat);
    				solver.addClause(clause);
    			}
    		}
    	}
    	
    	// STAGE 6 (No-Partial Axioms - Overloaded Operator Splitting)
    	// These axioms state that whenever any part of an operator is instantiated,
    	// so is the rest (some complete instantiation of the action is true).
    	// These axioms have to be added because we use factoring.
    	ArrayList<Integer> helper = null;
    	int currNumOfArgs = 0;
    	
    	// For each group of actions with the same name...
    	for (int j=0; j<groupActionsSameName.size()-1; j++) {
    		// Take a and b which are the borders of the action name we are processing now...
    		int a = groupActionsSameName.get(j);
    		int b = groupActionsSameName.get(j+1);
    		currNumOfArgs = this.ops_table.get(a).getName().getArity() + 1;
    		// Work for one specific argument (of the current action name) each time...
    		for (int k=1; k<currNumOfArgs; k++) {
    			// The helper ArrayList contains all the possible integers (splitted parts of action) 
    			// that correspond to the couple "current action name - current argument".
    			helper = new ArrayList<Integer>();
    			for (int l=a; l<b; l++) {
    				if ( !helper.contains(encodedActions.get(l).get(k)) ) {
    					helper.add(encodedActions.get(l).get(k));
    				}
    			}
    			
    			// For every timestep do...
    			for (int i=0; i<num_steps_inPlan; i++) {
    				int[] mat = new int[helper.size()+1];
    				mat[0] = - (encodedActions.get(a).get(0) + dimacsNum*i);
    				for (int l=0; l<helper.size(); l++) {
    					mat[l+1] = (Integer)helper.get(l) + dimacsNum*i;
    				}
    				clause = new VecInt(mat);
    				solver.addClause(clause);
    			}
    		}
    	}
    	
    	IProblem problem = solver;
    	// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
		int[] mysolution = problem.findModel();
		
		if (mysolution != null) {
			System.out.println("*** THE PROBLEM IS SATISFIABLE! ***");
			System.out.println();
			System.out.println("The proposed solution is the following:");
			System.out.println();
			
			// We translate the solution into an understandable form of a plan.
			this.translateSolutionOperatorSplitting(mysolution, dimacsNum, encodedActions);
			
        } else {
            System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
        }
		
    	return;
    }
    
    /**
     * Finds and displays a solution to our problem, provided that there exists one.
     * Otherwise, it declares the problem unsatisfiable.
     * The sat4j library is used to find the solution.
     * Encodes the actions of the problem using the method of Overloaded-Operator-Splitting.
     * It also uses the Classical Frame Axioms and the At-Least-One Axioms.
     * It implements the technique of factoring, in order to avoid combinatorial explosion,
     * when trying to convert clauses into CNF.
     * @throws ContradictionException, TimeoutException 
     */
    public void solveOverloadOpSplittClassFrameFactoring() throws ContradictionException, TimeoutException {

    	final int MAXVAR = 1000000;
    	final int NBCLAUSES = 500000;

    	ISolver solver = SolverFactory.newDefault();
    	//  prepare the solver to accept MAXVAR variables. MANDATORY
    	solver.newVar(MAXVAR);
    	// not mandatory for SAT solving. MANDATORY for MAXSAT solving
    	solver.setExpectedNumberOfClauses(NBCLAUSES);
    	// Feed the solver using Dimacs format, using arrays of int
    	// (best option to avoid dependencies on SAT4J IVecInt)

    	/**
    	 * We will use this variable in order to build all necessary clauses (one by one).
    	 */
    	VecInt clause;

    	// STAGE 1 (Initial State):
    	List<InitEl> inlist = problem.getInit();
    	for (int i=0; i<facts_table.size(); i++) { // for each fact
    		boolean isInit = false;
    		for (int j=0; j<inlist.size(); j++) { // for each "element" of the initial state...
        		if (facts_table.get(i).equals(inlist.get(j))) { // Find its "matching" entry in the facts table...
        			clause = new VecInt(new int[]{findDimacsIdFact(i, 0)});
        			solver.addClause(clause);
        			isInit = true ;
        			continue;
        		} 
    		}
    		if (!isInit){
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, 0)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// STAGE 2 (Goal State):
    	BitSet bs = goals[0]; // The positive preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	bs = goals[1]; // The negative preconditions of the goal
    	for (int i=0; i<bs.length(); i++) {
    		if (bs.get(i)) {
    			clause = new VecInt(new int[]{-findDimacsIdFact(i, num_steps_inPlan)});
    			solver.addClause(clause);
    		}
    	}
    	
    	// Stage 3 (Actions Encoding - OVERLOADED OPERATOR SPLITTING - Factored):
    	// We have to create one HashMap to encode every different action name with a different number.
    	HashMap<String, Integer> actionNamesHelper = new HashMap<String, Integer>();
    	// We have to create a matrix of HashMaps where each HashMap will be referring to the 'n' argument
    	// of the actions. When we will instantiate the matrix, its length will be equal to the number of arguments of the action
    	// which has the maximum number of arguments.
    	HashMap<Term, Integer>[] actionDataHelper;
    	// The encodedActions ArrayList will be used in the following way:
    	// Each element is an ArrayList that corresponds to a grounded action for the first timestep.
    	// Those (inner) ArrayLists contain the dimacs numbers of that grounded action (for the first timestep).
    	// The encoding of actions of other timesteps is based on this ArrayList,
    	// so we don't need to generate any other ArrayLists.
    	ArrayList<ArrayList<Integer>> encodedActions = new ArrayList<ArrayList<Integer>>();
    	// There is a correspondence between the encodedTerms and encoded ArrayLists.
    	// The encodedTerms has the corresponding Terms of actions, and is consulted
    	// when we do the refactoring.
    	ArrayList<ArrayList<Term>> encodedActionsTerms = new ArrayList<ArrayList<Term>>();
    	
    	// This ArrayList contains "pointers" which are used to define the limits of
    	// actions having the same name (this way we can "regroup" all instantiated actions).
    	ArrayList<Integer> groupActionsSameName = new ArrayList<Integer>();
    	
    	// The inner ArrayList that contains the dimacs numbers of a grounded action.
    	ArrayList<Integer> encoded = null;
    	// The inner ArrayList that contains the Terms of a grounded action.
    	ArrayList<Term> encodedTerms = null;
    	// This variable will be equal to the total number of different ints that are used in order to
    	// encode all split actions of a same timestep.
    	// It is used in every step in order to give a different encoding number to a (splitted) action.
    	int dimacsNum = 0;
    	// The number of arguments of the action which has the most arguments.
    	int maxArguments = 0;

    	// Fill the actionNamesHelper HashMap. 
    	String previousOpName = "";
    	// Helps us construct the groupActionsSameName ArrayList.
    	int pointerOfActionNames = 0;
    	for (int i=0; i<ops_table_size; i++) {
    		String currOpName = this.ops_table.get(i).getName().getPredicate();
    		if ( !currOpName.equals(previousOpName) ) {
    			// Constructing the groupActionsSameName ArrayList...
    			groupActionsSameName.add(pointerOfActionNames);
    			// We will provide a number for this action name.
    			dimacsNum++;
    			actionNamesHelper.put(currOpName, this.totalDimacsIdsFact + dimacsNum);
    			if (this.ops_table.get(i).getName().getArity() > maxArguments) {
    				// Update the maxArguments variable.
    				maxArguments = this.ops_table.get(i).getName().getArity();
    			}
    		}
    		previousOpName = currOpName;
    		pointerOfActionNames++;
    	}
    	// Add the last element to the groupActionsSameName ArrayList. It is now ready.
    	groupActionsSameName.add(ops_table_size);
    	
    	// Create the HashMaps of the actionDataHelper ArrayList.
    	actionDataHelper = new HashMap[maxArguments];
    	for (int i=0; i<maxArguments; i++) {	
    		actionDataHelper[i] = new HashMap<Term, Integer>();
    	}
    	// Fill the HashMaps and, at the same time, construct 
    	// the encodedActions and encodedActionsTerms ArrayLists.
    	for (int i=0; i<this.ops_table_size; i++) {
    		Op currAction = ops_table.get(i);
    		// We have to encode the current action.
    		encoded = new ArrayList<Integer>();
    		encodedTerms = new ArrayList<Term>();
    		// The first element of encoded is the number corresponding to the action's name.
    		encoded.add(actionNamesHelper.get(currAction.getName().getPredicate()));
    		// There exists no corresponding Term for the action's first part (the name).
    		encodedTerms.add(null);
    		// For every argument of the currAction we must check if we should put a new value to the corresponding HashMap,
    		// or if we just use a value that we already have there.
    		Iterator<Term> it = currAction.getName().iterator();
    		int ptr = 0;
    		while (it.hasNext()) {
    			Term currTerm = it.next();
    			if ( !actionDataHelper[ptr].containsKey(currTerm) ) {
    				// It's the first time we come across this term for this argument.
    				dimacsNum++;
    				actionDataHelper[ptr].put(currTerm, this.totalDimacsIdsFact + dimacsNum);
    				encoded.add(this.totalDimacsIdsFact + dimacsNum);
    				encodedTerms.add(currTerm);
    			} else {
    				// We have already come across this term for this argument.
    				encoded.add(actionDataHelper[ptr].get(currTerm));
    				encodedTerms.add(currTerm);
    			}
    			ptr++;
    		}
    		encodedActions.add(encoded);
    		encodedActionsTerms.add(encodedTerms);
    	}
    	
    	Fact currFact = null;
    	Iterator<Term> it = null;
    	Term term = null;
    	ArrayList<Integer> ans = null;
    	for (int i=0; i<ops_table_size; i++) {
    		for (int j=0; j<num_steps_inPlan; j++) {
    			// When relating an action to a fluent, we only need to include the parts of
    			// the action that have arguments appearing in the affected fluent,
    			// as well as the name of the action.
    			// For the POSITIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getPositivePreconditon();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							// for example: arm_empty
    						// (pickup) AND (Arg_1_a) --> arm_empty
    						// We factor the action by keeping only the name of the action (pickup).
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						// Also now (in overloaded-op-split) we have to keep the action's name...
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						// As well as (beginning from l=1)...
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							// We take the iterator over all the Terms of the currFact.
    							// For example, if currFact == (clear b), then
    							// the only term (on which we will iterate) is "b".
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact
    					ans.add(findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE PRECONDITIONS of actions...
    			bs = ops_table.get(i).getNegativePrecondition();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" because it is a negative precondition).
    					ans.add(-findDimacsIdFact(k, j));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the POSITIVE EFFECTS of actions...
    			bs = ops_table.get(i).getPositiveEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else { 
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact ("j+1" since we have an effect here).
    					ans.add(findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    			//  For the NEGATIVE EFFECTS of actions...
    			bs = ops_table.get(i).getNegativeEffect();
    			for (int k=0; k<bs.length(); k++) {
    				if (bs.get(k)) {
    					currFact = facts_table.get(k);
    					it = currFact.iterator();
    					
    					ans = new ArrayList<Integer>();
    					if (!it.hasNext()) {
							ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    					} else {
    						ans.add( -((Integer) encodedActions.get(i).get(0) + dimacsNum*j) );
    						for (int l=1; l<encodedActionsTerms.get(i).size(); l++) {
    							boolean found = false;
    							it = currFact.iterator();
    							while (it.hasNext()) {
    								term = it.next();
    								if (term.equals(encodedActionsTerms.get(i).get(l))) {
    									found = true;
    								}
    							}
    							if (found) {
    								// we are forced to keep this part of the action.
    								ans.add( -((Integer) encodedActions.get(i).get(l) + dimacsNum*j) );
    							}
    						}
    					}
    					// add the fact (Attention: "minus" and "j+1" because it is a negative effect).
    					ans.add(-findDimacsIdFact(k, j+1));
    					// create and add the clause
    					int[] mat = new int[ans.size()];
    					for (int x=0; x<ans.size(); x++) {
    						mat[x] = ans.get(x);
    					}
    					clause = new VecInt(mat);
    					solver.addClause(clause);
    				}
    			}
    		}
    	}
    	
    	// STAGE 4 (Classical Frame Axioms - Not Factored):
    	// If fluentF is not an effect of actionA, then:
    	// fluentF_i AND actionA_i --> fluentF_i+1  ======>  (NOT fluentF_i) OR (NOT actionA_i) OR fluentF_i+1
    	// (NOT fluentF_i) AND actionA_i --> (NOT fluentF_i+1)  ======>  fluentF_i OR (NOT actionA_i) OR (NOT fluentF_i+1)
    	// We will create clauses for each action which will impose that fluents not belonging
    	// to the effects of the action must remain the same after the action's execution.
    	// The difference to the Regular Encoding is that now all actions are "splitted" actions.
    	for (int i=0; i<ops_table_size; i++) {
    		Op curr = ops_table.get(i);
    		BitSet posEff = null;
			BitSet negEff = null;
 			// find the action's effects
			posEff = curr.getPositiveEffect();
			negEff = curr.getNegativeEffect();
			for (int j=0; j<facts_table_size; j++) {
				// If the fact is neither in the current action's positive effects,
				// nor in its negative effects, we should build a clause for the 
				// classical frame axiom. 
				if ( !posEff.get(j) && !negEff.get(j) ) {
					for (int k=0; k<num_steps_inPlan; k++) {
						ArrayList<Integer> temp = new ArrayList<Integer>();
						temp.add(-findDimacsIdFact(j, k));
						for (int l=0; l<encodedActions.get(i).size(); l++) {
							temp.add( -( (Integer)encodedActions.get(i).get(l) + dimacsNum*k) );
						}
						temp.add(findDimacsIdFact(j, k+1));
						int[] mat = new int[temp.size()];
						for (int l=0; l<mat.length; l++) {
							mat[l] = temp.get(l);
						}
						clause = new VecInt(mat);
						solver.addClause(clause);
						mat[0] = -mat[0];
						mat[mat.length-1] = -mat[mat.length-1];
						clause = new VecInt(mat);
						solver.addClause(clause);
					}
				}
    		}
    	}
    	
    	// STAGE 5 (At-Least-One Axioms - Factored)
    	// Factoring these axioms is essential in order to have a method that runs in acceptable time (at least in easy cases).
    	for (int i=0; i<num_steps_inPlan; i++) {
    		int[] mat = new int[encodedActions.size()];
    		for (int j=0; j<mat.length; j++) {
    			// Always take the first integer of each action.
    			mat[j] = (Integer) encodedActions.get(j).get(0) + dimacsNum * i;	
    		}
    		clause = new VecInt(mat);
			solver.addClause(clause);
    	}
    	
    	// STAGE 6 (No-Partial Axioms - Overloaded Operator Splitting)
    	// These axioms state that whenever any part of an operator is instantiated,
    	// so is the rest (some complete instantiation of the action is true).
    	// These axioms have to be added because we use factoring.
    	ArrayList<Integer> helper = null;
    	int currNumOfArgs = 0;
    	
    	// For each group of actions with the same name...
    	for (int j=0; j<groupActionsSameName.size()-1; j++) {
    		// Take a and b which are the borders of the action name we are processing now...
    		int a = groupActionsSameName.get(j);
    		int b = groupActionsSameName.get(j+1);
    		currNumOfArgs = this.ops_table.get(a).getName().getArity() + 1;
    		// Work for one specific argument (of the current action name) each time...
    		for (int k=1; k<currNumOfArgs; k++) {
    			// The helper ArrayList contains all the possible integers (splitted parts of action) 
    			// that correspond to the couple "current action name - current argument".
    			helper = new ArrayList<Integer>();
    			for (int l=a; l<b; l++) {
    				if ( !helper.contains(encodedActions.get(l).get(k)) ) {
    					helper.add(encodedActions.get(l).get(k));
    				}
    			}
    			// For every timestep do...
    			for (int i=0; i<num_steps_inPlan; i++) {
    				int[] mat = new int[helper.size()+1];
    				mat[0] = - (encodedActions.get(a).get(0) + dimacsNum*i);
    				for (int l=0; l<helper.size(); l++) {
    					mat[l+1] = (Integer)helper.get(l) + dimacsNum*i;
    				}
    				clause = new VecInt(mat);
    				solver.addClause(clause);
    			}
    		}
    	}
    	
    	IProblem problem = solver;
    	// We create a table of integers which holds the solution.
		// It contains positive and negative integers.
		int[] mysolution = problem.findModel();
		
		if (mysolution != null) {
			System.out.println("*** THE PROBLEM IS SATISFIABLE! ***");
			System.out.println();
			System.out.println("The proposed solution is the following:");
			System.out.println();
			
			// We translate the solution into an understandable form of a plan.
			this.translateSolutionOperatorSplitting(mysolution, dimacsNum, encodedActions);
			
        } else {
            System.out.println("%%% THE PROBLEM IS UNSATISFIABLE %%%");
        }
		
    	return;
    }
    
    /**
     * Translates the solution (in which the simple operator splitting technique was used to encode the actions),
     * from an array of integers, into an array of Strings (one for each timestep),
     * which represents the actual steps of the plan in an understandable format.
     * This method is called only if a solution (in the form of int[]) has already been found.
     * It is used both for Simple-Operator-Splitting and for Overloaded-Operator-Splitting.
     * 
     * @param solution
     * @param encodedActions 
     * @param dimacsNum 
     */
    public void translateSolutionOperatorSplitting(int[] solution,
    												int dimacsNum,
    												ArrayList<ArrayList<Integer>> encodedActions) {
    	// The length of the answer[] array is equal to the total number of steps in the plan.
    	// answer[i] corresponds to the i action of the plan we found. 
    	String[] answer = new String[get_numTimeSteps()];
    	
    	int totalLength = solution.length;
    	int usefulLength = totalLength - totalDimacsIdsFact;
    	
    	// We will only use the usefulSolution int[] from now on,
    	// because we only care about numbers of actions (not of facts).
    	int[] usefulSolution = new int[usefulLength];
    	for (int i=0; i<usefulSolution.length; i++) {
    		usefulSolution[i] = solution[totalDimacsIdsFact + i];
    	}
    	
    	int timestep = 0;
    	// for each timestep, the temp[] array will be properly constructed.
    	int[] temp = new int[dimacsNum]; 
    	// Each loop of the while represents another timestep.
    	while (timestep < num_steps_inPlan) {
    		// construct the array (temp) that will help us...
    		for (int i=0; i<dimacsNum; i++) {
    			temp[i] = usefulSolution[timestep*dimacsNum + i]; 	
    		}
    		
    		// We have to check each action (in a specific timestep),
    		// and find out if it is executed or not.
    		ArrayList<Integer> action = null;
    		// For each action...
    		for (int i=0; i<encodedActions.size(); i++) {
    			// get the next action...
    			action = encodedActions.get(i);
    			// The number of splitted parts of the action that have been given a value of true.
    			int matches = 0;
    			for (int j=0; j<action.size(); j++) {
    				for (int k=0; k<temp.length; k++) {
    					if ((Integer)action.get(j) == temp[k] - timestep*dimacsNum) {
        					matches++;
    					}
    				}	
    			}
    			// If the total number of matches found is equal to the number of the action's
    			// splitted parts, then we know that this action has been executed in this timestep. 
    			if (matches == action.size()) {
    				answer[timestep] = "TIMESTEP " + (timestep+1) + " : " + ops_table.get(i).getName().toString();
    				break;
    			} else {
    				answer[timestep] = "TIMESTEP " + (timestep+1) + " : " + "DO NOTHING";
    			}
    		}
    		timestep++;
    	}
    	// Print the plan we found
    	for (int i=0; i<answer.length; i++) {
    		System.out.println(answer[i]);
    	}
    	System.out.println();
    	
    	return;
    }
    
    /**
     * Translates the solution under the form of an array of integers, into an array of Strings
     * which represents the actual steps of the plan in an understandable format.
     * This method is called only if a solution (in the form of int[] has already been found).
     * @param solution
     */
    public void translateSolutionRegularEncoding(int[] solution) {
    	/**
    	 * The length of the array is equal to the total number of steps in the plan.
    	 * answer[i] corresponds to the i action of the plan. 
    	 */
    	String[] answer = new String[get_numTimeSteps()];
    	for (int i=0; i<solution.length; i++) {
    		int totalfacts = totalDimacsIdsFact;
    		if (solution[i] > totalfacts) {
    			// solution[i] corresponds to an action which must be executed in our plan (positive).
    			// It is not a fact.
    			// The division is used to find which is the action (according to the ops_table variable).
    			int act = ( solution[i] - totalfacts ) / get_numTimeSteps();
    			// The modulo is used to find the timestep of the action.
    			int time = ( solution[i]- totalfacts ) % get_numTimeSteps();
    			// Translation in case of time != 0
    			if (time != 0) {
    				String firstPart = "TIMESTEP " + time;
	    			String secondPart = ops_table.get(act).getName().toString();
	    			String answerElem = firstPart + " --> " + secondPart;
	    			answer[time-1] = answerElem;
    			} else { // If time == 0, we must be careful when translating.
    				String firstPart = "TIMESTEP " + get_numTimeSteps(); // It's the last action
    				String secondPart = ops_table.get(act-1).getName().toString();
	    			String answerElem = firstPart + " --> " + secondPart;
	    			answer[get_numTimeSteps()-1] = answerElem;
    			}
    		}	
    	}
    	// Fill the remaining slots of the array with a "DO NOTHING" value which corresponds
    	// to all timesteps where we have no action.
    	for (int i=0; i<answer.length; i++) {
    		if (answer[i] == null) {
    			answer[i] = "TIMESTEP " + (i+1) + " --> " + "DO NOTHING";
    		}
    	}
    	// Print the solution we found.
    	for (int i=0; i<answer.length; i++) {
    		System.out.println(answer[i]);
    	}
    	
    	System.out.println();
    	return;
    }
     
	/**
     * @param fact_id : the position of the fact in the facts table.
     * @param timestep : The timestep in which the fact is having place.
     * @return
     */
    private int findDimacsIdFact(int fact_id, int timestep) {
    	// We use (timestep+1) since we begin by giving the id 1 (and not 0) to the first fact.
		return ( fact_id*(num_steps_inPlan+1) + (timestep+1) );
	} 
    
    /**
     * Used only for the regular encoding of actions.
     * @param op_id : the position of the operation in the operations table.
     * @param timestep : The timestep in which the operation is having place.
     * @return
     */
    private int findDimacsIdOperationRegularEncoding(int op_id, int timestep) {
		return ( totalDimacsIdsFact + op_id*(num_steps_inPlan) + (timestep+1) );  
	}
    
    /**
     * Returns the total number of Dimacs Ids for all the facts.
     */
    public void findTotalDimacsIdsFact() {
    	totalDimacsIdsFact = (facts_table_size)*(num_steps_inPlan + 1);
		//return (facts_table_size)*(num_steps_inPlan + 1);
    	return;
	}

	/**
	 * Used only for the regular encoding of actions.
     * Returns the total number of Dimacs Ids 
     * given to all facts and all operations (for all timesteps). 
     * @return
     */
    public int findTotalDimacsIdsRegularEncoding() {
    	return (facts_table_size)*(num_steps_inPlan + 1) + 
    			(ops_table_size)*(num_steps_inPlan);	
    }
    
    /**
     * Returns the number of time steps that we use in order to find a solution.
     * @return
     */
    public int get_numTimeSteps() {
    	return num_steps_inPlan;
    }
    
    /**
     * Sets the number of time steps that we use in order to find a solution.
     * @return
     */
    public void set_numTimeSteps(int n) {
    	num_steps_inPlan = n; 
    }
       
}
