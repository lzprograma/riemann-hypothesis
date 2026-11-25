module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LayerApproximation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_ext :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R' : Type) [CommRing R'] [Algebra O R'] (I : Ideal R') [IsHausdorff I R'] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R → maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∀ f f' : R →ₐ[O] R', (∃ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, f x ∈ I ∧ f' x ∈ I) → f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f' := by
  intro O _ _ R _ _ _ B _ _ _ R' _ _ I _ i S hS hm f f' ⟨n, hn⟩ hi hs
  have hT : ∀ t ∈ S ∪ i '' (maximalIdeal B : Set B), t ∈ AlgHom.equalizer f f' ∧ t ∈ maximalIdeal R := by
    rintro t (ht | ⟨b, hb, rfl⟩)
    · exact ⟨hs t ht, hS ht⟩
    · refine ⟨DFunLike.congr_fun hi b, ?_⟩
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hb
  have hm' : maximalIdeal R ≤ Ideal.span (S ∪ i '' (maximalIdeal B : Set B)) ⊔ maximalIdeal R ^ 2 := by
    rw [Ideal.span_union]
    exact hm
  have key : ∀ g : R →ₐ[O] R', (∀ x ∈ maximalIdeal R ^ n, g x ∈ I) →
      ∀ k : ℕ, ∀ x ∈ maximalIdeal R ^ (n * k), g x ∈ I ^ k := by
    intro g hg k x hx
    rw [pow_mul] at hx
    have hle : (maximalIdeal R ^ n) ^ k ≤ (I ^ k).comap (g : R →+* R') :=
      le_trans (Ideal.pow_right_mono (fun y hy => hg y hy) k) (Ideal.le_comap_pow _ k)
    exact hle hx
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  obtain ⟨a, ha, h⟩ := _root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx
    (maximalIdeal R) (AlgHom.equalizer f f') _ (IsCO.res_surj (O := O)) hT hm' (n * k) x
  have ha' : f a = f' a := ha
  have : f x - f' x = f (x - a) - f' (x - a) := by rw [map_sub, map_sub, ha']; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, this]
  exact sub_mem (key f (fun y hy => (hn y hy).1) k _ h) (key f' (fun y hy => (hn y hy).2) k _ h)
