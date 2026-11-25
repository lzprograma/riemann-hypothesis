module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dualBasis_coord_mem_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M)) (l : Module.Dual O M), (∀ w, l w ∈ IsLocalRing.maximalIdeal O) → ∀ j, lb.repr l j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ M _ _ _ _ k lb l hl j
  haveI : Module.Free O M := Module.free_of_flat_of_isLocalRing
  let ε := Module.Free.chooseBasis O M
  have hsum : l = ∑ i, l (ε i) • ε.dualBasis i := by
    refine ε.ext fun a => ?_
    simp

  rw [hsum, map_sum]
  simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hl _)

end GlobalTheory
