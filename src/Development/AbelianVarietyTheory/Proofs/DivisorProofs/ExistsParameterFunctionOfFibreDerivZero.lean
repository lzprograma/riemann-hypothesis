module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

theorem exists_glue_fn {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (hK : K.Rich) (a : ∀ k, Hol (K.W k)) (ha : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k') :
    ∃ G : Tot I g → ℂ, ∀ k, ∀ q ∈ K.W k, G q = (a k).fn q := by
  classical
  have key : ∀ k₁ k₂ q, q ∈ K.W k₁ → q ∈ K.W k₂ → (a k₁).fn q = (a k₂).fn q := by
    intro k₁ k₂ q h₁ h₂
    obtain ⟨k, hk, e₁, e₂⟩ := hK.2 0 k₁ k₂ q h₁ (by rw [F.shift_zero]; exact h₂)
    have r₁ := fn_sh e₁ (a k₁) hk
    have r₂ := fn_sh e₂ (a k₂) hk
    rw [ha, F.shift_zero] at r₁ r₂
    rw [← r₁, ← r₂]
  refine ⟨fun q ↦ if h : ∃ k, q ∈ K.W k then (a h.choose).fn q else 0, fun k q hq ↦ ?_⟩
  have h : ∃ k, q ∈ K.W k := ⟨k, hq⟩
  simp only [dite_eq_left h]
  exact key _ _ q h.choose_spec hq

theorem exists_cst_of_dw_eq_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k') →
    (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  intro I _ g Λ _ F K hK a ha hd
  obtain ⟨G, hG⟩ := exists_glue_fn K hK a ha
  have ev : ∀ k, ∀ q ∈ K.W k, G =ᶠ[𝓝 q] (a k).fn := fun k q hq ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hq] with r hr using hG k r hr
  have an : ∀ q : Tot I g, q.1 ∈ F.V → AnalyticAt ℂ G q := fun q hq ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    exact ((a k).analytic q hk).congr (ev k q hk).symm
  have d0 : ∀ q : Tot I g, q.1 ∈ F.V → ∀ i, fderiv ℂ G q ((0, Pi.single i 1) : Tot I g) = 0 := fun q hq i ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    rw [(ev k q hk).fderiv_eq, ← Hol.fn_der _ _ hk]
    change (dw i (a k)).fn q = 0
    rw [hd, ← Hol.ev_apply q hk, map_zero]
  have cs : ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0) := fun z hz w ↦ by
    have hf : ∀ w : Fin g → ℂ, HasFDerivAt (fun w ↦ G (z, w))
        ((fderiv ℂ G (z, w)).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ))) w := fun w ↦
      (an (z, w) hz).differentiableAt.hasFDerivAt.comp w (hasFDerivAt_prodMk_right z w)
    refine is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun w ↦ G (z, w)) (fun w ↦ (hf w).differentiableAt)
      (fun w ↦ ?_) w 0
    rw [(hf w).fderiv]
    ext v
    have hv : ((0, v) : Tot I g) = ∑ i, v i • ((0, Pi.single i 1) : Tot I g) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    change fderiv ℂ G (z, w) (0, v) = 0

    rw [hv, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, d0 (z, w) hz i, smul_zero]
  refine ⟨Hol.mk (fun z ↦ G (z, 0)) fun z hz ↦
    AnalyticAt.comp (g := G) (f := fun z ↦ ((z, 0) : Tot I g)) (an (z, 0) hz)
      (analyticAt_id.prod analyticAt_const), fun k ↦ Hol.ext_fn fun q hq ↦ ?_⟩
  rw [fn_cst _ _ _ hq, ← hG k q hq]
  exact (cs q.1 (K.base k q hq) q.2).trans (Hol.fn_mk (fun z ↦ G (z, 0)) _ (K.base k q hq)).symm

end GlobalTheory.AnPer.Charts
