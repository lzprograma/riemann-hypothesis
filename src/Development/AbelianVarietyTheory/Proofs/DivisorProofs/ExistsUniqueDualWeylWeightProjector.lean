module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.UG

namespace GlobalTheory.ExpFrame

def rowProj (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (w : Fin N → ℕ) :
    dualWeyl O N N ν →ₗ[O] dualWeyl O N N ν :=
  (weightedHomogeneousComponent (rowW N N) w).restrict
    (fun x hx => dualWeylModuleRowGraded O N N ν w x hx)

theorem exists_unique_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι)
    (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  intro O _ N ι _ _ lam τ w
  have hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w)) := by
    intro x y hy
    unfold atFactor
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp only [Function.update_self, LinearMap.restrict_apply, rowProj]
      exact Subtype.ext hy.symm
    · simp [Function.update_of_ne h]
  refine ⟨_, hP, fun a' ha' => ?_⟩
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  exact (ha' x y rfl).trans (hP x y rfl).symm

end GlobalTheory.ExpFrame

end
