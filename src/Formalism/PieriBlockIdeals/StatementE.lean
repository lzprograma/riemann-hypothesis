module

public import Formalism.MirabolicMackeyTheory.StatementT
public import Formalism.PieriBlockIdeals.TailInequalityEventually
public import Formalism.QuotientMetricDivisors.ClassSumDualLe

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.CohomologicalDescent.E

open Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

def ExIntervalLt : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ l : ℕ, l.Prime → ∀ (lo : ℤ) (w : ℕ),
    (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
    LA.exZ N N le_rfl (res N lam) l ≤ N.choose 2 * Nat.log l w ∧
      (w < l → LA.exZ N N le_rfl (res N lam) l = 0)

def ExCut : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ l : ℕ, l.Prime → ∀ (lo : ℤ) (w : ℕ),
    (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
    ∀ a : ℕ, a ≤ N →
      LA.exZ N N le_rfl (res N lam) l ≤
        LA.exZ a a le_rfl (res a lam) l +
          LA.exZ (N - a) (N - a) le_rfl (res (N - a) (fun i => lam (a + i))) l +
          a * (N - a) * Nat.log l w

section SF09

open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

end SF09

section Record

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
  Formalism.CohomologicalDescent.LargeParameterEstimates

end Record

end Formalism.CohomologicalDescent.E
