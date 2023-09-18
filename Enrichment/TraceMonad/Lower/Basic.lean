import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.UpperLower
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

structure LowerTraces (ε τ α) [PartialOrder ε] where
  terminating: α -> LowerSet ε
  nonterminating: Set τ