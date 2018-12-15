# Concolic search

This bundle provides a Ciao extension of depth-first search that
allows the explicit annotation of constraints that must be considered
in path exploration ("path conditions") and those that are not, and
uses constraint-based model extraction to explore new paths. We call
it "concolic search" due to the similarities with "concolic testing"
algorithms.

Additionally, these libraries include interfacing with external SMT
solvers. This allows using constraints from external theories,
symbolic manipulation of constraints (meta-programming), explicit
satisfability checks, model extractions, etc. 

