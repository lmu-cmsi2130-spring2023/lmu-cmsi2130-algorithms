package main.csp;

import java.security.KeyStore.LoadStoreParameter;
import java.time.LocalDate;
import java.util.*;
import java.util.concurrent.RecursiveAction;

import javax.swing.text.StyledEditorKit.BoldAction;

/**
 * CSP: Calendar Satisfaction Problem Solver
 * Provides a solution for scheduling some n meetings in a given
 * period of time and according to some unary and binary constraints
 * on the dates of each meeting.
 */
public class CSPSolver {

    // Backtracking CSP Solver
    // --------------------------------------------------------------------------------------------------------------

    /**
     * Public interface for the CSP solver in which the number of meetings,
     * range of allowable dates for each meeting, and constraints on meeting
     * times are specified.
     * 
     * @param nMeetings   The number of meetings that must be scheduled, indexed
     *                    from 0 to n-1
     * @param rangeStart  The start date (inclusive) of the domains of each of the n
     *                    meeting-variables
     * @param rangeEnd    The end date (inclusive) of the domains of each of the n
     *                    meeting-variables
     * @param constraints Date constraints on the meeting times (unary and binary
     *                    for this assignment)
     * @return A list of dates that satisfies each of the constraints for each of
     *         the n meetings,
     *         indexed by the variable they satisfy, or null if no solution exists.
     */
    public static List<LocalDate> solve(int nMeetings, LocalDate rangeStart, LocalDate rangeEnd,
            Set<DateConstraint> constraints) {

        ArrayList<MeetingDomain> domains = new ArrayList<>();
        for (int i = 0; i < nMeetings; i++) {
            MeetingDomain meeting = new MeetingDomain(rangeStart, rangeEnd);
            domains.add(meeting);
        }
        nodeConsistency(domains, constraints);
        arcConsistency(domains, constraints);
        return recursiveBacktracking(new ArrayList<LocalDate>(), constraints, domains, nMeetings);
    }

    /**
     * Implements csp backtracking in order to recursively solve the csp
     * 
     * @param assignment  list of local dates that holds the dates for the meetings
     * @param constraints Date constraints on the meeting times (unary and binary
     *                    for this assignment)
     * @param domains     list of meeting domains which are indexed by meeting
     *                    variable
     * @param nMeetings   The number of meetings that must be scheduled, indexed
     *                    from 0 to n-1
     *
     * @return A list of dates that satisfies each of the constraints for each of
     *         the n meetings,
     *         indexed by the variable they satisfy, or null if no solution exists.
     */
    private static List<LocalDate> recursiveBacktracking(ArrayList<LocalDate> assignment,
            Set<DateConstraint> constraints,
            ArrayList<MeetingDomain> domains, int nMeetings) {

        if (assignment.size() == nMeetings) {
            return assignment;
        }
        for (MeetingDomain value : domains) {
            for (LocalDate date : value.domainValues) {
                assignment.add(date);
                if (isSatisfied(assignment, constraints)) {
                    List<LocalDate> result = recursiveBacktracking(assignment, constraints, domains, nMeetings);
                    if (result != null) {
                        return result;
                    }
                }
                assignment.remove(assignment.size() - 1);
            }
        }
        return null;
    }

    /**
     * informs on whether or not the given assignments satify the given constraints
     * 
     * @param assignment  list of local dates that holds the dates for the meetings
     * @param constraints Date constraints on the meeting times (unary and binary
     *
     * @return true or false to whether or not two dates are satisfied by the
     *         constraints
     */
    private static boolean isSatisfied(ArrayList<LocalDate> assignment, Set<DateConstraint> constraints) {

        for (DateConstraint date : constraints) {
            if (date.L_VAL >= assignment.size()) {
                continue;
            }
            LocalDate leftDate = assignment.get(date.L_VAL);
            LocalDate rightDate;
            if (date.arity() == 1) {
                rightDate = ((UnaryDateConstraint) date).R_VAL;
            } else {
                BinaryDateConstraint binaryDate = ((BinaryDateConstraint) date);
                if (binaryDate.R_VAL >= assignment.size()) {
                    continue;
                }
                rightDate = assignment.get(binaryDate.R_VAL);
            }
            if (!date.isSatisfiedBy(leftDate, rightDate)) {
                return false;
            }
        }
        return true;
    }

    // Filtering Operations
    // --------------------------------------------------------------------------------------------------------------

    /**
     * Enforces node consistency for all variables' domains given in varDomains
     * based on
     * the given constraints. Meetings' domains correspond to their index in the
     * varDomains List.
     * 
     * @param varDomains  List of MeetingDomains in which index i corresponds to D_i
     * @param constraints Set of DateConstraints specifying how the domains should
     *                    be constrained.
     *                    [!] Note, these may be either unary or binary constraints,
     *                    but this method should only process
     *                    the *unary* constraints!
     */
    public static void nodeConsistency(List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {

        for (DateConstraint date : constraints) {
            if (date.arity() == 1) {
                varDomains.get((date.L_VAL));
                LocalDate rightDate = ((UnaryDateConstraint) date).R_VAL;
                Set<LocalDate> tempAssignment = new HashSet<>();
                for (LocalDate domain : varDomains.get((date.L_VAL)).domainValues) {
                    tempAssignment.add(domain);
                    if (date.isSatisfiedBy(domain, rightDate)) {
                        continue;
                    } else {
                        tempAssignment.remove(domain);
                    }
                }
                varDomains.get((date.L_VAL)).domainValues = tempAssignment;
            }
        }
    }

    /**
     * Enforces arc consistency for all variables' domains given in varDomains based
     * on
     * the given constraints. Meetings' domains correspond to their index in the
     * varDomains List.
     * 
     * @param varDomains  List of MeetingDomains in which index i corresponds to D_i
     * @param constraints Set of DateConstraints specifying how the domains should
     *                    be constrained.
     *                    [!] Note, these may be either unary or binary constraints,
     *                    but this method should only process
     *                    the *binary* constraints using the AC-3 algorithm!
     */
    public static void arcConsistency(List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {
        Set<Arc> cspArcs = new HashSet<>();

        for (DateConstraint dateConstraint : constraints) {
            if (dateConstraint.arity() == 2) {

                int binaryLeftDate = dateConstraint.L_VAL;
                BinaryDateConstraint binaryRightConstraint = ((BinaryDateConstraint) dateConstraint);
                Arc arc1 = new Arc(binaryLeftDate, binaryRightConstraint.R_VAL, dateConstraint);
                Arc arc2 = new Arc(binaryRightConstraint.R_VAL, binaryLeftDate, binaryRightConstraint.getReverse());
                cspArcs.add(arc1);
                cspArcs.add(arc2);
            }
        }
        Set<Arc> tempNeighbors = new HashSet<>(cspArcs);
        while (!cspArcs.isEmpty()) {
            Iterator<Arc> iterator = cspArcs.iterator();
            Arc first = iterator.next();
            iterator.remove();
            if (removeInconsistentValues(first, varDomains)) {
                System.out.println(varDomains);
                for (Arc arcs : tempNeighbors) {
                    if (arcs.HEAD == first.TAIL) {
                        cspArcs.add(arcs);
                    }
                }
            }
        }
    }

    /**
     * takes in an arc and list of meeting domains and pruned the values that are
     * unnecessary
     * 
     * @param tailOrHead an arc in which the head and tail are the meeting indexes
     *                   corresponding with Meeting variables and their associated
     *                   domains.
     * @param varDomains List of MeetingDomains in which index i corresponds to D_i
     *
     * @return true or false to whether or inconsistent values have been removed
     */
    private static Boolean removeInconsistentValues(Arc tailOrHead, List<MeetingDomain> varDomains) {

        boolean removed = false;
        List<LocalDate> temp = new ArrayList<>();
        for (LocalDate tailDate : varDomains.get(tailOrHead.TAIL).domainValues) {
            boolean isSatisfied = false;
            for (LocalDate headDate : varDomains.get(tailOrHead.HEAD).domainValues) {
                if (tailOrHead.CONSTRAINT.isSatisfiedBy(tailDate, headDate)) {
                    isSatisfied = true;
                }
            }
            if (!isSatisfied) {
                temp.add(tailDate);
                removed = true;
            }
        }
        varDomains.get(tailOrHead.TAIL).domainValues.removeAll(temp);
        return removed;
    }

    /**
     * Private helper class organizing Arcs as defined by the AC-3 algorithm, useful
     * for implementing the
     * arcConsistency method.
     * [!] You may modify this class however you'd like, its basis is just a
     * suggestion that will indeed work.
     */
    private static class Arc {

        public final DateConstraint CONSTRAINT;
        public final int TAIL, HEAD;

        /**
         * Constructs a new Arc (tail -> head) where head and tail are the meeting
         * indexes
         * corresponding with Meeting variables and their associated domains.
         * 
         * @param tail Meeting index of the tail
         * @param head Meeting index of the head
         * @param c    Constraint represented by this Arc.
         *             [!] WARNING: A DateConstraint's isSatisfiedBy method is
         *             parameterized as:
         *             isSatisfiedBy (LocalDate leftDate, LocalDate rightDate), meaning
         *             L_VAL for the first
         *             parameter and R_VAL for the second. Be careful with this when
         *             creating Arcs that reverse
         *             direction. You may find the BinaryDateConstraint's getReverse
         *             method useful here.
         */
        public Arc(int tail, int head, DateConstraint c) {
            this.TAIL = tail;
            this.HEAD = head;
            this.CONSTRAINT = c;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (this.getClass() != other.getClass()) {
                return false;
            }
            Arc otherArc = (Arc) other;
            return this.TAIL == otherArc.TAIL && this.HEAD == otherArc.HEAD
                    && this.CONSTRAINT.equals(otherArc.CONSTRAINT);
        }

        @Override
        public int hashCode() {
            return Objects.hash(this.TAIL, this.HEAD, this.CONSTRAINT);
        }

        @Override
        public String toString() {
            return "(" + this.TAIL + " -> " + this.HEAD + ")";
        }

    }

}
