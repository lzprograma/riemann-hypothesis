module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cob_of_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases ha : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ (z g)).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    rw [hm g, ha g, one_mul, sub_self]
  · push Not at ha
    obtain ⟨g₀, hg₀⟩ := ha
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.2 hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ _).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    have key : φ ((a g₀ - 1)⁻¹ • z g₀) = m := by
      rw [map_smul, hm g₀, smul_eq_mul, ← sub_one_mul, inv_mul_cancel_left₀ hne]
    rw [map_sub, map_sub, map_smul, key, hm g, smul_eq_mul, sub_self]

theorem UpperTheory.V.GradeZeroInterpolatingElement.xvanExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + red (γ g : c.O) * z h) → D.UnrT z 0 → (∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = red (γ g : c.O) * m - m) → ∃ m, ∀ g, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD k _ red hred γ hγ z hz hcoc hunr hloc
  have hlh : IsLocalHom red := ⟨fun a ha => by
    by_contra hn
    have h0 := hred a ((mem_maximalIdeal a).2 hn)
    rw [h0] at ha
    exact not_isUnit_zero ha⟩
  letI : Algebra (ResidueField c.O) k := (ResidueField.lift red).toAlgebra
  have hι : ∀ a : c.O, red a = algebraMap (ResidueField c.O) k (residue c.O a) := fun a =>
    (ResidueField.lift_residue_apply red a).symm
  have hX : D.XVan γ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hD.xvan D.al (by simp)).1
    · exact (hD.xvan D.be (by simp)).1
    · exact (hD.xvan D.th (by simp)).1
    · exact (hD.xvan D.al (by simp)).2
    · exact (hD.xvan D.be (by simp)).2
    · exact (hD.xvan D.th (by simp)).2
  simp only [hι]
  apply cob_of_coord (fun g => Raw.bar γ g) z
  intro φ
  have h1 : ∀ g h, φ (z (g * h)) = φ (z g) + Raw.bar γ g * φ (z h) := by
    intro g h
    rw [hcoc g h, map_add (f := _), hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have h2 : D.UnrT (fun g => φ (z g)) 0 := by
    intro A hA g hg hb
    simp only [hunr A hA g hg hb, map_zero]
  have h3 : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, φ (z g) = Raw.bar γ g * m - m := by
    intro v hv
    obtain ⟨m, hm⟩ := hloc v hv
    refine ⟨φ m, fun g hg => ?_⟩
    rw [hm g hg, hι, ← Algebra.smul_def, map_sub, map_smul, smul_eq_mul]
  exact hX (fun g => φ (z g)) (hz.comp fun x => φ x) h1 h2 h3
