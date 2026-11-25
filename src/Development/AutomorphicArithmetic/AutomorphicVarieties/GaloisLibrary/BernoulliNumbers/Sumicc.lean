module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BOneSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumicc :
    ∀ {M : Type} [AddCommMonoid M] {N : ℕ} [NeZero N] (G : ZMod N → M), ∑ a ∈ Icc 1 N, G (a : ZMod N) = ∑ a : ZMod N, G a := by
  apply _root_.UpperTheory.V.Bern.b_one_sum <;> assumption
