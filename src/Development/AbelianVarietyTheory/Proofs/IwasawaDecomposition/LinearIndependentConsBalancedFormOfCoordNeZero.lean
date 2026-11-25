module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem linearIndependent_cons_of_coord_ne_zero :
    ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    c j ≠ 0 → j ∉ Set.range e → LinearIndependent ℤ (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
  intro O _ bar X _ _ m p δ β c j e hδ hβ hcj hj
  rw [Fintype.linearIndependent_iff] at hδ ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg

  have hgB : g 0 • (β : LinearMap.BilinForm ℤ X) + ∑ k, g k.succ • (δ (e k) : LinearMap.BilinForm ℤ X) = 0 := by
    have := congrArg Subtype.val hg
    simpa [Submodule.coe_sum] using this

  let s : Fin m → ℝ := fun i => ∑ k, if e k = i then (g k.succ : ℝ) else 0
  let r : Fin m → ℝ := fun i => (g 0 : ℝ) * c i + s i
  have hind : ∀ (d : Fin 0 → ℤ) (a : Fin m → ℤ),
      ∑ i, a i • (δ i : LinearMap.BilinForm ℤ X) = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → a = 0 := by
    intro d a h
    have h' : ∑ i, a i • δ i = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum] using h
    funext i
    exact hδ a h' i
  have hrel : ∑ i, r i • toReal (δ i : LinearMap.BilinForm ℤ X) =
      ∑ k : Fin 0, (0 : Fin 0 → ℝ) k • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    apply LinearMap.ext₂
    intro x y
    have h1 := LinearMap.congr_fun₂ hβ x y
    have h2 := LinearMap.congr_fun₂ hgB x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, LinearMap.add_apply, smul_eq_mul,
      LinearMap.zero_apply] at h1 h2
    have h2' : (g 0 : ℝ) * (((β : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) + ∑ k, (g k.succ : ℝ) * (((δ (e k) : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) = 0 := by
      exact_mod_cast h2
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, Finset.univ_eq_empty,
      Finset.sum_empty, LinearMap.zero_apply]
    rw [← h2', h1]
    simp only [r, s, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul, mul_assoc]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hr : r = 0 := eq_zero_of_toReal_rel hind hrel
  have hsj : s j = 0 := Finset.sum_eq_zero fun k _ => by
    rw [ite_eq_right]
    intro h
    exact hj ⟨k, h⟩
  have hg0 : g 0 = 0 := by
    have := congrFun hr j
    simp only [r, hsj, add_zero, Pi.zero_apply] at this
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hcj
  intro i
  refine Fin.cases hg0 (fun k => ?_) i
  have := congrFun hr (e k)
  have hs : s (e k) = (g k.succ : ℝ) := by
    simp only [s]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      rw [ite_eq_right]
      exact fun h => hk' (e.injective h)
    · simp
  simp only [r, hs, hg0, Int.cast_zero, zero_mul, zero_add, Pi.zero_apply] at this
  exact_mod_cast this

end GlobalTheory.PolFan
