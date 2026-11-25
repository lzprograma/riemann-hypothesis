module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

namespace Bl.general_b_fact_third_further

theorem goal1 :
  ∀ (f : Real → Complex),
  Continuous.{0, 0} f →
    (∀ (s t : Real), Eq.{1} (f (HAdd.hAdd.{0, 0, 0} s t)) (HMul.hMul.{0, 0, 0} (f s) (f t))) →
      (∀ (s : Real), Eq.{1} (Norm.norm.{0} (f s)) 1) →
        Exists.{1} fun (b : Real) ↦
          ∀ (s : Real),
            Eq.{1} (f s) (Complex.exp (HMul.hMul.{0, 0, 0} (Complex.ofReal (HMul.hMul.{0, 0, 0} b s)) Complex.I)) := by
  intro f hc hm hn
  have h0 : f 0 = 1 := by
    have hne : f 0 ≠ 0 := fun h' => (zero_ne_one (α := ℝ)) (by simpa [h'] using hn 0)
    exact (mul_left_cancel₀ hne (by simpa using hm 0 0)).symm
  let F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, f t
  have hFd : ∀ x, HasDerivAt F (f x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    by_contra hcon; push Not at hcon
    have h1 := hFd 0; rw [show F = fun _ => (0 : ℂ) from funext hcon] at h1
    exact one_ne_zero (h0 ▸ h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))
  have key : ∀ s, f s * F δ = F (s + δ) - F s := fun s => by
    simp only [F, ← intervalIntegral.integral_const_mul, ← hm]
    rw [intervalIntegral.integral_comp_add_left f s, add_zero,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  let a : ℂ := (f δ - 1) / F δ
  have hfd : ∀ s, HasDerivAt f (a * f s) s := fun s => by
    have e : f = fun x => (F (x + δ) - F x) / F δ := funext fun x => by rw [← key x, mul_div_cancel_right₀ _ hδ]
    have hd : HasDerivAt (fun x => (F (x + δ) - F x) / F δ) ((f (s + δ) - f s) / F δ) s :=
      (((hFd (s + δ)).comp_add_const s δ).sub (hFd s)).div_const (F δ)
    rw [← e] at hd; convert hd using 1; rw [hm, show a = (f δ - 1) / F δ from rfl]; field_simp
  have hg : ∀ s, HasDerivAt (fun x : ℝ => f x * Complex.exp (-(a * x))) 0 s := fun s =>
    ((hfd s).mul (((hasDerivAt_id (s : ℂ)).const_mul a).comp_ofReal.neg.cexp)).congr_deriv (by simp; ring)
  have ha : ∀ s : ℝ, f s = Complex.exp (a * s) := fun s => by
    have hcst := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) s 0
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, h0, Complex.exp_neg] at hcst
    exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hcst
  have hre : a.re = 0 := by simpa [ha 1, Complex.norm_exp] using hn 1
  exact ⟨a.im, fun s => by rw [ha]; congr 1; apply Complex.ext <;> simp [hre]⟩

end Bl.general_b_fact_third_further
