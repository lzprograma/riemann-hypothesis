module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive
public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.LFunctionBounds.ExpSumLowerBound
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZF

theorem rdp_rectInt_eq_fx (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :
    rectInt g x0 x1 y0 y1 = Formalism.FX.rectInt g x0 x1 y0 y1 := rfl

theorem rdp_rectInt_add (f1 f2 : ℂ → ℂ) (x0 x1 y0 y1 : ℝ)
    (hB1 : IntervalIntegrable (fun x : ℝ => f1 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hB2 : IntervalIntegrable (fun x : ℝ => f2 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hT1 : IntervalIntegrable (fun x : ℝ => f1 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hT2 : IntervalIntegrable (fun x : ℝ => f2 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hR1 : IntervalIntegrable (fun y : ℝ => f1 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hR2 : IntervalIntegrable (fun y : ℝ => f2 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hL1 : IntervalIntegrable (fun y : ℝ => f1 (x0 + y * I)) MeasureTheory.volume y0 y1)
    (hL2 : IntervalIntegrable (fun y : ℝ => f2 (x0 + y * I)) MeasureTheory.volume y0 y1) :
    rectInt (fun w => f1 w + f2 w) x0 x1 y0 y1 =
      rectInt f1 x0 x1 y0 y1 + rectInt f2 x0 x1 y0 y1 := by
  simp only [rectInt]
  rw [intervalIntegral.integral_add hB1 hB2, intervalIntegral.integral_add hT1 hT2,
    intervalIntegral.integral_add hR1 hR2, intervalIntegral.integral_add hL1 hL2]
  ring

theorem rdp_seg (g G : ℂ → ℂ) (a b p : ℂ) (γ : ℝ → ℂ) (s t : ℝ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun u => G (γ u)) (Set.uIcc s t)) (hP : ∀ u ∈ Set.uIcc s t, γ u ≠ p)
    (hg : ∀ w : ℂ, w ≠ p → g w = G w + a / (w - p) ^ 2 + b / (w - p)) :
    IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
    IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
  have hD : ContinuousOn (fun u => a / (γ u - p) ^ 2) (Set.uIcc s t) := by
    refine ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun u hu => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 (hP u hu))
  have hS : ContinuousOn (fun u => G (γ u) + b / (γ u - p)) (Set.uIcc s t) := by
    refine hG.add (ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun u hu => ?_))
    exact sub_ne_zero.2 (hP u hu)
  refine ⟨(hS.congr fun u hu => ?_).intervalIntegrable, hD.intervalIntegrable⟩
  rw [hg _ (hP u hu)]
  ring

theorem rectangle_double_pole : RectDoublePole := by
  intro g G a b p x0 x1 y0 y1 h1 h2 h3 h4 hU hg
  obtain ⟨U, hUo, hRU, hGU⟩ := hU
  have hGc : ContinuousOn G U := hGU.continuousOn
  have hx01 : x0 ≤ x1 := by linarith
  have hy01 : y0 ≤ y1 := by linarith

  have hmem : ∀ x y : ℝ, x ∈ Set.uIcc x0 x1 → y ∈ Set.uIcc y0 y1 → (x : ℂ) + y * I ∈ U := by
    intro x y hx hy
    apply hRU
    rw [Complex.mem_reProdIm]
    simp [hx, hy]
  have hseg : ∀ (γ : ℝ → ℂ) (s t : ℝ), Continuous γ → (∀ u ∈ Set.uIcc s t, γ u ∈ U) →
      (∀ u ∈ Set.uIcc s t, γ u ≠ p) →
      IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
      IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
    intro γ s t hγ hγU hγp
    exact rdp_seg g G a b p γ s t hγ (hGc.comp hγ.continuousOn fun u hu => hγU u hu) hγp hg
  have hxl : x0 ∈ Set.uIcc x0 x1 := Set.left_mem_uIcc
  have hxr : x1 ∈ Set.uIcc x0 x1 := Set.right_mem_uIcc
  have hyl : y0 ∈ Set.uIcc y0 y1 := Set.left_mem_uIcc
  have hyr : y1 ∈ Set.uIcc y0 y1 := Set.right_mem_uIcc
  have hB := hseg (fun x : ℝ => (x : ℂ) + y0 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y0 hu hyl)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hT := hseg (fun x : ℝ => (x : ℂ) + y1 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y1 hu hyr)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hR := hseg (fun y : ℝ => (x1 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x1 u hxr hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hL := hseg (fun y : ℝ => (x0 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x0 u hxl hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hdouble : rectInt (fun w => a / (w - p) ^ 2) x0 x1 y0 y1 = 0 :=
    GlobalTheory.ResRect.bdInt_sq h1 h2 h3 h4 a
  have hsplit : g = fun w => (g w - a / (w - p) ^ 2) + a / (w - p) ^ 2 := by
    funext w; ring
  rw [hsplit, rdp_rectInt_add _ _ x0 x1 y0 y1 hB.1 hB.2 hT.1 hT.2 hR.1 hR.2 hL.1 hL.2,
    hdouble, add_zero, rdp_rectInt_eq_fx]
  have hres := Formalism.FX.rectangle_residue (fun w => g w - a / (w - p) ^ 2) G {p} (fun _ => b)
    x0 x1 y0 y1 (by linarith) (by linarith) (by simp [h1, h2, h3, h4]) ⟨U, hUo, hRU, hGU⟩
    (by
      intro w hw
      have hwp : w ≠ p := by simpa using hw
      simp only [Finset.sum_singleton]
      rw [hg w hwp]
      ring)
  simpa using hres

end Formalism.ZF
