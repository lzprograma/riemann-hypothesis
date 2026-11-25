module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.DefsOC
public import Formalism.ZetaNonvanishing.MellinSAux
public import Formalism.ZetaNonvanishing.MellinSgen
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.MellinInversion
import Mathlib.Tactic.Lemma

@[expose] public section

open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

lemma perron_Sz_eq_Sa : Formalism.Sz = Formalism.Sa (fun n => (Λ n : ℝ)) := rfl

lemma perron_Sz_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : Formalism.Sz x = 0 := by
  unfold Formalism.Sz
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hx0 : 0 ≤ x := by
    by_contra! h
    have h1 := Nat.floor_of_nonpos h.le
    omega
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 hn.2
  have hn1 : n = 1 := by
    have h1 : (n : ℝ) ≤ 1 := hnx.trans hx
    have h2 : n ≤ 1 := by exact_mod_cast h1
    omega
  subst hn1
  simp [ArithmeticFunction.vonMangoldt_apply_one]

lemma perron_Sz_continuousAt (y : ℝ) : ContinuousAt (fun x => (Formalism.Sz x : ℂ)) y := by
  rw [perron_Sz_eq_Sa]
  exact (Complex.continuous_ofReal.comp
    (Formalism.Sa_continuous (fun n => (Λ n : ℝ)))).continuousAt

lemma perron_norm_LSeries_le {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖LSeries ↗Λ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
  have hs : LSeriesSummable ↗Λ (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have heq : ∀ n, ‖LSeries.term ↗Λ w n‖ = ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
    intro n
    simp [LSeries.norm_term_eq, hw]
  unfold LSeries
  calc ‖∑' n, LSeries.term ↗Λ w n‖ ≤ ∑' n, ‖LSeries.term ↗Λ w n‖ :=
        norm_tsum_le_tsum_norm (hs.norm.congr fun n => (heq n).symm)
    _ = ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by simp_rw [heq]

lemma perron_denom_bound {σ₀ : ℝ} (hσ : 1 < σ₀) (t : ℝ) :
    min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) ≤ ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖ := by
  set m := min ((σ₀ - 1) ^ 2) 1 with hm
  have hm0 : 0 ≤ m := le_min (sq_nonneg _) zero_le_one
  have hm1 : m ≤ 1 := min_le_right _ _
  have hm2 : m ≤ (σ₀ - 1) ^ 2 := min_le_left _ _
  have hn1 : ‖((σ₀ : ℂ) + t * I)‖ ^ 2 = σ₀ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hn2 : ‖((σ₀ : ℂ) + t * I - 1)‖ ^ 2 = (σ₀ - 1) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have a0 : 0 ≤ m * (1 + t ^ 2) := by positivity
  have a1 : m * (1 + t ^ 2) ≤ σ₀ ^ 2 + t ^ 2 := by nlinarith
  have a2 : m * (1 + t ^ 2) ≤ (σ₀ - 1) ^ 2 + t ^ 2 := by nlinarith
  have key : (m * (1 + t ^ 2)) ^ 2 ≤ (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [sq]
    exact mul_le_mul a1 a2 a0 (by positivity)
  have e : (‖((σ₀ : ℂ) + t * I)‖ * ‖((σ₀ : ℂ) + t * I - 1)‖) ^ 2 =
      (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [mul_pow, hn1, hn2]
  rw [norm_mul]
  exact (pow_le_pow_iff_left₀ a0 (by positivity) two_ne_zero).1 (key.trans e.symm.le)

lemma perron_continuous_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  have hU : ∀ t : ℝ, 1 < ((σ₀ : ℂ) + t * I).re := fun t => by simpa using hσ
  have hzd : DifferentiableOn ℂ riemannZeta {s : ℂ | 1 < s.re} := fun s hs =>
    (differentiableAt_riemannZeta (fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hderiv : ContinuousOn (deriv riemannZeta) {s : ℂ | 1 < s.re} :=
    ((hzd.analyticOnNhd hopen).deriv).continuousOn
  have hline : Continuous (fun t : ℝ => (σ₀ : ℂ) + t * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  unfold Fy
  refine Continuous.div (Continuous.mul (Continuous.neg (Continuous.div ?_ ?_ ?_)) ?_) ?_ ?_
  · exact hderiv.comp_continuous hline hU
  · exact hzd.continuousOn.comp_continuous hline hU
  · intro t
    exact riemannZeta_ne_zero_of_one_lt_re (hU t)
  · exact hline.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  · exact hline.mul (hline.sub continuous_const)
  · intro t
    have h1 := hU t
    refine mul_ne_zero ?_ ?_
    · intro h
      rw [h] at h1
      norm_num at h1
    · intro h
      rw [sub_eq_zero] at h
      rw [h] at h1
      simp at h1

lemma perron_integrable_of_bounded {g : ℂ → ℂ} {y σ B : ℝ} (hy : 0 < y) (hσ : 1 < σ)
    (hg : ∀ t : ℝ, ‖g ((σ : ℂ) + t * I)‖ ≤ B)
    (hcont : Continuous (fun t : ℝ => let w := (σ : ℂ) + t * I
      g w * (y : ℂ) ^ w / (w * (w - 1)))) :
    Integrable (fun t : ℝ => let w := (σ : ℂ) + t * I
      g w * (y : ℂ) ^ w / (w * (w - 1))) := by
  let d := min ((σ - 1) ^ 2) 1
  have hd : 0 < d := lt_min (sq_pos_of_pos (sub_pos.mpr hσ)) one_pos
  have hB := (norm_nonneg _).trans (hg 0)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (B * y ^ σ / d))
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  calc _ ≤ B * y ^ σ / (d * (1 + t ^ 2)) :=
        div_le_div₀ (mul_nonneg hB (Real.rpow_nonneg hy.le _))
          (mul_le_mul_of_nonneg_right (hg t) (Real.rpow_nonneg hy.le _)) (by positivity)
          (perron_denom_bound hσ t)
    _ = _ := by rw [div_mul_eq_div_div, div_eq_mul_inv _ (1 + t ^ 2)]

lemma perron_integrable_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  refine perron_integrable_of_bounded (B := ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖)
    (g := fun w => -(deriv riemannZeta w / riemannZeta w)) hy hσ ?_ (perron_continuous_Fy hy hσ)
  intro t
  have hw : 1 < ((σ₀ : ℂ) + t * I).re := by simpa using hσ
  rw [← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  exact perron_norm_LSeries_le hσ _ (by simp)

lemma perron_mellinSgen_Λ :
    Measurable (Formalism.Sa (fun n => (Λ n : ℝ))) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Formalism.Sa (fun n => (Λ n : ℝ)) x| * x ^ (-σ - 1))
      (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Formalism.Sa (fun n => (Λ n : ℝ)) x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => ((Λ n : ℝ) : ℂ)) s / (s * (s - 1)) := Formalism.mellinSgen (fun n => (Λ n : ℝ)) 1 (fun n => by
    rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg])

lemma perron_mellin_Sz {w : ℂ} (hw : 1 < w.re) :
    mellin (fun x : ℝ => (Formalism.Sz x : ℂ)) (-w) =
      -(deriv riemannZeta w / riemannZeta w) / (w * (w - 1)) := by
  have h1 := perron_mellinSgen_Λ.2.2 w hw
  rw [← perron_Sz_eq_Sa] at h1
  rw [mellin]
  have hzero : ∀ t ∈ Ioi (0:ℝ) \ Ioi 1, (t : ℂ) ^ (-w - 1) • ((Formalism.Sz t : ℝ) : ℂ) = 0 := by
    intro t ht
    have : t ≤ 1 := not_lt.1 ht.2
    rw [perron_Sz_eq_zero_of_le_one this]
    simp
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) hzero]
  simp_rw [smul_eq_mul, mul_comm ((_ : ℂ) ^ (-w - 1))]
  rw [h1, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  ring

lemma perron_mellinConvergent {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => (Formalism.Sz x : ℂ)) ((-σ₀ : ℝ) : ℂ) := by
  unfold MellinConvergent
  have h2 := perron_mellinSgen_Λ.2.1 σ₀ hσ
  rw [← perron_Sz_eq_Sa] at h2
  have hmeas : Measurable Formalism.Sz := by
    rw [perron_Sz_eq_Sa]; exact perron_mellinSgen_Λ.1
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (((-σ₀ : ℝ) : ℂ) - 1) • ((Formalism.Sz t : ℝ) : ℂ)) (Ioi 1) := by
    refine Integrable.mono' h2 ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.pow_const _).smul
        (Complex.continuous_ofReal.measurable.comp hmeas)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.norm_real,
        Real.norm_eq_abs]
      simp [mul_comm]
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ hI1
  refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp [perron_Sz_eq_zero_of_le_one ht.2]

lemma perron_verticalIntegrable {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => (Formalism.Sz x : ℂ))) (-σ₀) := by
  unfold VerticalIntegrable
  have hF := (perron_integrable_Fy one_pos hσ).comp_neg
  have heq : (fun y : ℝ => mellin (fun x : ℝ => (Formalism.Sz x : ℂ)) (((-σ₀ : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => Fy 1 ((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    funext y
    have hre : 1 < ((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I).re := by simpa using hσ
    rw [show ((-σ₀ : ℝ) : ℂ) + y * I = -((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I) by push_cast; ring,
      perron_mellin_Sz hre]
    unfold Fy
    simp [Complex.one_cpow]
  rw [heq]
  exact hF

theorem perron_formula : Perron := by
  intro y hy σ₀ hσ
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  refine ⟨perron_integrable_Fy hy0 hσ, ?_⟩
  have hinv := mellinInv_mellin_eq (-σ₀) (fun x : ℝ => (Formalism.Sz x : ℂ)) hy0 (perron_mellinConvergent hσ)
    (perron_verticalIntegrable hσ) (perron_Sz_continuousAt y)
  rw [← hinv, mellinInv, Complex.real_smul]
  push_cast
  congr 1
  have hneg := integral_neg_eq_self (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) volume
  rw [← hneg]
  congr 1
  funext t
  have hre : 1 < ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I).re := by simpa using hσ
  rw [show -(σ₀ : ℂ) + t * I = -((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) by push_cast; ring,
    perron_mellin_Sz hre, neg_neg]
  unfold Fy
  rw [smul_eq_mul]
  ring

end Formalism.ZF
