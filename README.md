PlanningWithConstraints
========================

In this project we implement a planer which, given a **_STRIPS_** (https://en.wikipedia.org/wiki/STRIPS) representation of a domain,
is able to compute a way to start from a specific configuration A and, by performing some actions, end up in a "goal" configuration B.
An example is the **_blocksworld domain_**, where an initial configuration of blocks must be rearranged.
This rearrangement (plan) is a series of picking up some blocks and stacking them on each other.

In this project, the configurations, the actions and their effects are encoded in the form of **constraints**.
Thus, every planing problem is encoded as a set of constraints, and then a Constraint Solver is called 
to compute the solution (the required plan).

Some important files used: **_pddl4j.jar_** (for the domain descriptions) and **_sat4j-1.7.jar_** (SAT solver).

This project was a collaborative work with **_Julien Marçais_**.