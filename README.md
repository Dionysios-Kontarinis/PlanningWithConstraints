PlanningWithConstraints
========================

This project implements a planer which, given a **_STRIPS_** (https://en.wikipedia.org/wiki/STRIPS) representation of a domain,
is able to compute a way to start from a specific configuration A and, by performing some actions, end up in a "goal" configuration B.
An example is the **_blocksworld domain_**, where an initial configuration of blocks must be rearranged.
This rearrangement (plan) is a series of picking up some blocks and stacking them on each other.

In this project, the configurations, the actions and their effects are encoded in the form of **constraints**.
Thus, every planing problem is encoded as a set of constraints, and a Constraint Solver is called to compute the solution (the required plan).

Some important files used: pddl4j.jar (for the domain descriptions) and sat4j-1.7.jar (SAT solver).

This project was a collaborative work with **_Julien Marçais_**.