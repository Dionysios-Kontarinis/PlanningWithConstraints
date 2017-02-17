import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import pddl4j.InvalidExpException;
import pddl4j.PDDLObject;
import pddl4j.exp.AndExp;
import pddl4j.exp.AtomicFormula;
import pddl4j.exp.Exp;
import pddl4j.exp.ExpID;
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
 * This class defines usefull method to manipulate planning problem.
 *
 * @author Damien Pellier
 * @version 1.0 
 * Created on 6 juin 08
 */
public final class Utilities {

    /**
     * Default constructor.
     */
    private Utilities() { }
    
    /**
     * Enumerates all the facts of the planning problem.
     * 
     * @param pb the planning problem.
     * @return The list of instantiated fact of the specified problem.
     */
    public static List<Fact> instantiateFacts(final PDDLObject pb) {
        final List<Fact> facts = new ArrayList<Fact>(100);
        final Iterator<AtomicFormula> i = pb.predicatesIterator();
        while (i.hasNext()) {
            final AtomicFormula skeleton = i.next();
            final List<Term> args = new ArrayList<Term>();
            for (Term arg: skeleton) {
                args.add(arg);
            }
            Utilities.rec_instantiateFacts(pb, facts, skeleton, args, new Substitution());
        }
        return facts;
    }
    
    /**
     * Instantiates all the fact from a specific atomic formula skeleton of the
     * problem.
     * 
     * @param pb the planning problem.
     * @param facts the list of already instantiated fact of the specified problem.
     * @param skeleton the atomic formula skeleton to instantiate.
     * @param args the list of arguments of the atomic formula skeleton not yet
     *            instantiated.
     * @param sigma the map containing for each argument already instantiated its
     *            value.
     */
    private static void rec_instantiateFacts(final PDDLObject pb, 
                final List<Fact> facts,
                final AtomicFormula skeleton,
                final List<Term> args,
                final Substitution sigma) {
        if (args.isEmpty()) {
            final Fact fact = new Fact(skeleton.apply(sigma), facts.size());
            facts.add(fact);
        } else {
            final Variable var = (Variable) args.get(0);
            final Set<Constant> values = pb.getTypedDomain(var.getTypeSet());
            for (Constant c : values) {
                sigma.bind(var, c);
                final List<Term> newArgs = new ArrayList<Term>(args);
                final Term t = newArgs.remove(0);
                Utilities.rec_instantiateFacts(pb, facts, skeleton, newArgs, sigma);
            }
            
        }
    }
    
    /**
     * Enumerates all the operators of the planning problem.
     * 
     * @param pb the planning problem
     * @param facts the list of already instantiated facts.
     * @return the list of instantiated operators.
     * 
     * @throws InvalidExpException if an expression of an operator of the
     *             problem is not an accepted PDDL expression.
     */
    public static List<Op> instantiateOps(final PDDLObject pb,
                final List<Fact> facts) throws InvalidExpException {
        // Generate the noop action first so a noop action as the same index as
        // its corresponding fact.
        final List<Op> ops = new ArrayList<Op>(100);
        for (int i = 0; i < facts.size(); i++) {
            Utilities.addNewNoOp(ops, facts.get(i));
        }
        final Iterator<ActionDef> i = pb.actionsIterator();
        while (i.hasNext()) {
            final ActionDef a = i.next();
            if (a.getActionID().equals(ActionID.ACTION)) {
                final Action op = (Action) a;
                final List<Term> parameters = new ArrayList<Term>(op.getParameters());
                Utilities.rec_instantiateOps(pb, ops, facts, op, parameters, new Substitution());
            } 
        }
        return ops;
    }
    
    /**
     * Instantiates all the operator from a specific action of the problem.
     * 
     * @param pb the planning problem.
     * @param ops the list of already instantiated operators.
     * @param facts he list of already instantiated facts.
     * @param action the atomic formula skeleton to instantiate.
     * @param param the list of parameters of the action not yet instantiated.
     * @param sigma the map containing for each parameter already instantiated its
     *            value.
     * @throws InvalidExpException if an invalid PDDL expression is found in
     *             the action.
     */
    private static void rec_instantiateOps(final PDDLObject pb,
                final List<Op> ops, 
                final List<Fact> facts,
                final Action action,
                final List<Term> param,
                final Substitution sigma)
                throws InvalidExpException {

        if (param.isEmpty()) {
            Utilities.addNewOp(ops, action, facts, sigma);
        } else {
            final Variable var = (Variable) param.get(0);
            final Set<Constant> values = pb.getTypedDomain(var.getTypeSet());
            for (Constant c : values) {
                sigma.bind(var, c);
                final List<Term> newParam = new ArrayList<Term>(param);
                newParam.remove(0);
                Utilities.rec_instantiateOps(pb, ops, facts, action, newParam, sigma);
            }
        }
    }

    /**
     * Creates a new noop operator from a specific fact.
     * 
     * @param ops the list of already instantiated operators.
     * @param fact the fact.
     */
    private static void addNewNoOp(final List<Op> ops, final Fact fact) {
        final AtomicFormula name = fact.clone();
        name.setPredicate("noop-" + name.getPredicate());
        final BitSet pp = new BitSet();
        pp.set(fact.getId());
        final BitSet np = new BitSet();
        final BitSet pe = new BitSet();
        pe.set(fact.getId());
        final BitSet ne = new BitSet();
        final Op op = new Op(name, pp, np, pe, ne, ops.size());
        ops.add(op);
    }
    
    /**
     * Add a new operator created from a specific PDDL action.
     * 
     * @param ops the list of already instantiated operators.
     * @param action the action.
     * @param facts the list of already instantiated facts.
     * @param sigma the mapping between the parameters and their values.
     * @return <code>true</code> if a new operator is added; <code>false</code> otherwise.
     * @throws InvalidExpException if the unexpected PDDL expression occurs in
     *             the action definition.
     */
    private static boolean addNewOp(final List<Op> ops,
                final Action action, 
                final List<Fact> facts,
                final Substitution sigma)
                throws InvalidExpException {
        boolean added = false;
        final AtomicFormula name = new AtomicFormula(action.getName());
        for (Term p : action.getParameters()) {
            name.add((Constant) sigma.getBinding((Variable) p));
        }
        final BitSet[] pre = Utilities.expToBitSet(action.getPrecondition().apply(sigma), facts); 
        if (pre != null) {
            final BitSet[] eff = Utilities.expToBitSet(action.getEffect().apply(sigma), facts);
            final Op op = new Op(name, pre[0], pre[1], eff[0], eff[1], ops.size());
            ops.add(op);
            added = true;
        } 
        return added;
    }
    
    /**
     * Transforms a PDDL expression into a bit set representation.
     * 
     * @param exp the expression to transform.
     * @param facts the list of already instantiated facts.
     * @return a array of bit set with a length of 2 such the first bit set
     *         represents the positive fact of the expression and second bit set
     *         that represents the negative fact of the expression.
     * @throws InvalidExpException if an sub expression of the specified
     *             expression is not valid.
     */
    public static BitSet[] expToBitSet(final Exp exp, final List<Fact> facts) 
            throws InvalidExpException {
        final BitSet[] bitSet = new BitSet[2]; 
        bitSet[0] = new BitSet();
        bitSet[1] = new BitSet();
        Set<Literal> literals = null;
        
        literals = Utilities.toLiteralSet(exp);
        if (literals != null) {
            for (Literal literal : literals) {
                if (literal.getExpID().equals(ExpID.ATOMIC_FORMULA)) {
                    final AtomicFormula predicate = (AtomicFormula) literal;
                    final int index = facts.indexOf(predicate);
                    bitSet[0].set(index);
                } else {
                    final NotAtomicFormula notExp = (NotAtomicFormula) literal;
                    final AtomicFormula predicate = (AtomicFormula) notExp.getExp();
                    final int index = facts.indexOf(predicate);
                    bitSet[1].set(index);
                }
            }
            return bitSet;
        } else {
            return null;
        }
        
    }
    
    /**
     * Converts a ground PDDL expression into a set of literals.
     * 
     * @param exp the expression that must be converted.
     * @return a set of literal that represents the specified expression.
     * @throws InvalidExpException if an sub expression of the specified
     *             expression is not valid.
     */
    private static Set<Literal> toLiteralSet(final Exp exp) throws InvalidExpException {
        final Set<Literal> literals = new HashSet<Literal>();

        final Stack<Exp> stack = new Stack<Exp>();
        stack.add(exp);
        boolean failure = false;
        
        while (!stack.isEmpty() && !failure) {
            final Exp e = stack.pop();
            switch (e.getExpID()) {
            case AND:
                final AndExp andExp = (AndExp) e;
                for (Exp sexp : andExp) {
                    stack.push(sexp);
                }
                break;
            case ATOMIC_FORMULA:
                final AtomicFormula p = (AtomicFormula) e;
                literals.add(p.clone());
                break;
            case F_COMP:
                final FCompExp fcomp = (FCompExp) e;
                failure = !fcomp.evaluate();
                break;
            case NOT:
                final NotExp notExp = (NotExp) e;
                final Exp nexp = notExp.getExp();
                switch (nexp.getExpID()) {
                case F_COMP:
                    final FCompExp sfc = (FCompExp) nexp;
                    failure = sfc.evaluate();
                    break;
                default:
                    final Set<Literal> pl = Utilities.toLiteralSet(notExp.getExp());
                    if (pl != null) {
                        for (Literal l : pl) {
                            final NotAtomicFormula f = new NotAtomicFormula((AtomicFormula) l);
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
}
