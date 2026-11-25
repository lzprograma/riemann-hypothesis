module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameChartMeasure
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

@[expose] public section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Ortho

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData GlobalTheory.SW.Slab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

noncomputable def tri (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => ((mat (bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

end GlobalTheory.Ker.Ortho

namespace GlobalTheory.Ker

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
theorem _root_.GlobalTheory.Ker.exists_orthonormalisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ o b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, ∀ x ∈ X.dom, _root_.GlobalTheory.Ker.IsONFr X (o x) ∧ b x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r ∧ x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (o x) (b x) ∧ (∀ (τ : X.Ψ) (i : Fin r), ‖b x τ i i‖ ^ 2 = ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖) ∧ ∀ u : X.Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ (τ : X.Ψ) v w, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm v w) → X.lmulC u x ∈ X.dom ∧ o (X.lmulC u x) = X.lmulC u (o x) := by
  intro E _ _ _ r X
  have hBor : ∀ x ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := fun x hx => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
  have hdetB : ∀ x ∈ X.dom, ∀ τ, IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det := fun x hx τ =>
    isUnit_iff_ne_zero.2 (hBor x hx τ).1
  obtain ⟨δ₀, hδ₀, hslab⟩ := _root_.GlobalTheory.SW.thin_slab E r X
  have hslab0 := hslab δ₀ hδ₀ le_rfl
  have hfac : ∀ x ∈ X.dom,
      x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) (_root_.GlobalTheory.Ker.Ortho.tri X x) := by
    intro x hx
    funext τ
    show x τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (hdetB x hx τ)]
    rfl
  have hON : ∀ x ∈ X.dom, _root_.GlobalTheory.Ker.IsONFr X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) :=
    fun x hx => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
  have hOdom : ∀ x ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) ∈ X.dom := fun x hx =>
    hslab0.2.1 (hslab0.2.2.1 _ (hON x hx))
  have hTri : ∀ x ∈ X.dom, _root_.GlobalTheory.Ker.Ortho.tri X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := by
    intro x hx
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
    simp only [Set.mem_ofPred_eq]
    intro τ
    have hu := hdetB x hx τ
    haveI := Matrix.invertibleOfIsUnitDet _ hu
    refine ⟨left_ne_zero_of_mul_eq_one (Matrix.det_nonsing_inv_mul_det _ hu), fun a c hca => ?_⟩
    exact Matrix.blockTriangular_inv_of_blockTriangular (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.upper_of_bor X (hBor x hx) τ) hca
  have hsgn : ∀ i : Fin (r + 1), ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.GlobalTheory.SW.sgnM X) i‖ = 1 := by
    intro i
    rw [_root_.GlobalTheory.SW.Slab.lminor_sgnM]
    rcases _root_.GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> simp [h]
  have hdminON : ∀ x ∈ X.dom, ∀ τ i,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro x hx τ i
    show ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ)) i‖ = 1
    rw [hON x hx τ, hsgn]
  have hdiag : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin r), ‖_root_.GlobalTheory.Ker.Ortho.tri X x τ i i‖ ^ 2 =
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := by
    intro x hx τ i
    have h := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ratio_rmul X _ (hOdom x hx) (hTri x hx) τ i
    rw [← hfac x hx] at h
    rw [h, norm_div, hdminON x hx, hdminON x hx, div_one, mul_one]
  have hequiv : ∀ x ∈ X.dom, ∀ u : X.Ψ → Matrix (Fin r) (Fin r) ℂ,
      (∀ (τ : X.Ψ) v w, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm v w) →
      X.lmulC u x ∈ X.dom ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (X.lmulC u x) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X (X.lmulC u x)) =
        X.lmulC u (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) := by
    intro x hx u hu
    have hg : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ) =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := fun τ =>
      _root_.GlobalTheory.SW.Slab.gram_lmulC X hu τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
    have hdm : ∀ τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (X.lmulC u x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := fun τ i => by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
      rw [hg τ]
    refine ⟨?_, ?_⟩
    · have hx' := hx
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hx' ⊢
      simp only [Set.mem_ofPred_eq] at hx' ⊢
      intro τ
      obtain ⟨-, hpos⟩ := hx' τ
      refine ⟨fun h0 => ?_, fun i => by rw [hdm τ i]; exact hpos i⟩
      have hl := hpos (Fin.last r)
      have hlast : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ (Fin.last r) = (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)).det := by
        unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
        rfl
      have hdg := _root_.GlobalTheory.SW.Slab.det_gram X τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ)
      rw [hg τ, h0] at hdg
      simp only [zero_mul, map_zero] at hdg
      rw [hlast, hdg] at hl
      simp at hl
    · have hB : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X (X.lmulC u x) = _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x := by
        funext τ
        show _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X (X.lmulC u x) τ * diagonal (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X (X.lmulC u x) τ) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ * diagonal (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X x τ)
        have hO : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X (X.lmulC u x) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ := by
          unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf
          rw [hg τ]
        have hS : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X (X.lmulC u x) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X x τ := by
          unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dOf
          rw [hO]
          have h2 : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ) =
              _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ) := by
            rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ = u τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ from rfl, Matrix.mul_assoc]
            exact _root_.GlobalTheory.SW.Slab.gram_lmulC X hu τ _
          rw [h2]
        rw [hO, hS]
      rw [hB]
      funext τ
      show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ =
        u τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)
      rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ = u τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ from rfl, Matrix.mul_assoc]
  exact ⟨fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x), _root_.GlobalTheory.Ker.Ortho.tri X,
    fun x hx => ⟨hON x hx, hTri x hx, hfac x hx, hdiag x hx, fun u hu => hequiv x hx u hu⟩⟩

end GlobalTheory.Ker
