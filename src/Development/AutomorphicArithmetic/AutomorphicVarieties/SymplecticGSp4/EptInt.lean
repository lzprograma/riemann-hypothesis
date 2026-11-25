module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EiiUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (ha0 : 0 ≤ a) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  apply _root_.UpperTheory.V.Loc.spl_cont <;> assumption

theorem UpperTheory.V.GradeZeroInterpolatingElement.eptInt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → Continuous r ∧ (∀ g i j, ‖r g i j - D.r0E g i j‖ < 1) ∧ ∃ c' : Coef l, c.O ≤ c'.O ∧ (∀ g i j, r g i j ∈ c'.O) ∧ ∀ i, ∃ (s : Finset (G ℚ Ω)) (a : G ℚ Ω → PadicAlgCl l), (∀ g, a g ∈ c'.O) ∧ Matrix.single i i (1 : PadicAlgCl l) = ∑ g ∈ s, a g • r g := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, _, _, _, ρ, y, hρ, rfl⟩ := hr
  obtain ⟨⟨c', hc', hy'⟩, a, ha1, ha0, hy⟩ := (coPt c R).1 y
  refine ⟨?_, fun g i j => ?_, c', hc', fun g i j => hy' _, fun i => ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact cont_of_adic (maximalIdeal R) (y : R →+* PadicAlgCl l) a ha1 ha0 hy _ (ρ.cont i j)
  · have hm : ρ.hom g i j - algebraMap c.O R (D.r0 g i j) ∈ maximalIdeal R ^ 1 := by
      rw [pow_one, ← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, ρ.red, sub_eq_zero]
      rfl
    have h := hy 1 _ hm
    rw [map_sub, AlgHom.commutes, pow_one] at h
    exact lt_of_le_of_lt h ha1
  · have h := eii D hD R ρ hρ.mult hρ.nrm i
    obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h
    refine ⟨b.support, fun g => y (b g), fun g => hy' _, ?_⟩
    ext p q
    have h2 := congrArg y (congrFun (congrFun hb p) q)

    rw [Finsupp.sum, Matrix.sum_apply, map_sum] at h2
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul] at h2 ⊢
    have h3 : y (Matrix.single i i (1 : R) p q) = Matrix.single i i (1 : PadicAlgCl l) p q := by
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [← h3, ← h2]
    rfl
