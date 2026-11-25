module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

open Complex Filter Topology Asymptotics
open scoped BigOperators Real

namespace GlobalTheory.LocalCube

private lemma norm_le_div_mul_norm_of_schwarz {φ : ℂ → ℂ} {ρ c : ℝ}
    (hd : DifferentiableOn ℂ φ (Metric.ball 0 ρ)) (h0 : φ 0 = 0)
    (hc : ∀ t ∈ Metric.ball (0 : ℂ) ρ, ‖φ t‖ ≤ c) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ) :
    ‖φ t‖ ≤ c / ρ * ‖t‖ := by
  simpa [h0, dist_zero_right] using Complex.dist_le_div_mul_dist_of_mapsTo_ball hd
    (fun s hs => by simpa [h0, mem_closedBall_zero_iff] using hc s hs) ht

private lemma isBigO_norm_cube_of_analytic_vanishing_coords {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {u : (Fin 3 → V) → ℂ} (ha : AnalyticAt ℂ u 0)
    (hv : ∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → V), x a = 0 → u x = 0) :
    u =O[𝓝 0] fun z => ‖z‖ ^ 3 := by
  have hu0 : u 0 = 0 := (hv 0).self_of_nhds rfl
  have hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → V),
      DifferentiableAt ℂ u x ∧ ‖u x‖ < 1 ∧ ∀ a, x a = 0 → u x = 0 :=
    (ha.eventually_analyticAt.mono fun _ hx => hx.differentiableAt).and
      ((ha.continuousAt.norm.eventually (gt_mem_nhds (by simp [hu0]))).and
        (Filter.eventually_all.2 hv))
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine IsBigO.of_bound (1 / R ^ 3) ?_
  filter_upwards [Metric.ball_mem_nhds 0 hR] with y hy
  simp only [norm_pow, norm_norm]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [hu0]
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  set ρ := R / ‖y‖ with hρdef
  have hρ : 0 < ρ := div_pos hR hyn
  have h0ρ : ‖(0 : ℂ)‖ < ρ := by simpa using hρ
  have h1ρ : ‖(1 : ℂ)‖ < ρ := by simpa using (one_lt_div hyn).2 (mem_ball_zero_iff.1 hy)
  let p : (Fin 3 → ℂ) → (Fin 3 → V) := fun t a => t a • y a
  have hpb : ∀ t, (∀ a, ‖t a‖ < ρ) → p t ∈ Metric.ball 0 R := fun t ht => by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hR]
    intro a
    calc ‖t a • y a‖ = ‖t a‖ * ‖y a‖ := norm_smul _ _
      _ ≤ ‖t a‖ * ‖y‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm y a) (norm_nonneg _)
      _ < ρ * ‖y‖ := mul_lt_mul_of_pos_right (ht a) hyn
      _ = R := by rw [hρdef]; field_simp
  have hGz : ∀ t a, (∀ i, ‖t i‖ < ρ) → t a = 0 → u (p t) = 0 := fun t a ht ha0 =>
    (hball _ (hpb t ht)).2.2 a (by simp [p, ha0])
  have hstep : ∀ (t : Fin 3 → ℂ) (a : Fin 3) (c : ℝ) (d : ℂ),
      (∀ i, ‖t i‖ < ρ) → (d = 0 → u (p t) = 0) →
      (∀ s, ‖s‖ < ρ → ‖u (p (Function.update t a s))‖ ≤ c * ‖d‖) →
      ‖u (p t)‖ ≤ (c / ρ * ‖t a‖) * ‖d‖ := by
    intro t a c d ht hd0 hb
    rcases eq_or_ne d 0 with rfl | hd
    · simp [hd0 rfl]
    have hn : 0 < ‖d‖ := norm_pos_iff.2 hd
    have hupd : ∀ s, ‖s‖ < ρ → ∀ i, ‖Function.update t a s i‖ < ρ := fun s hs i => by
      by_cases hi : i = a <;> simp [hi, hs, ht i]
    have hdiff : DifferentiableOn ℂ (fun s => u (p (Function.update t a s))) (Metric.ball 0 ρ) := by
      intro s hs
      have hpeq : (fun s' : ℂ => p (Function.update t a s')) =
          fun s' => p t + (s' - t a) • (Pi.single a (y a) : Fin 3 → V) := by
        funext s' i
        by_cases hi : i = a
        · subst hi; simp [p, sub_smul]
        · simp [p, hi]
      have hfd : DifferentiableAt ℂ (fun s' : ℂ => p (Function.update t a s')) s := by
        rw [hpeq]; fun_prop
      exact ((hball _ (hpb _ (hupd s (mem_ball_zero_iff.1 hs)))).1.comp s hfd).differentiableWithinAt
    have key := norm_le_div_mul_norm_of_schwarz (φ := fun s => u (p (Function.update t a s)) / d)
      (hdiff.div_const d)
      (by rw [hGz _ a (hupd 0 h0ρ) (Function.update_self a 0 t), zero_div])
      (fun s hs => by rw [norm_div, div_le_iff₀ hn]; exact hb s (mem_ball_zero_iff.1 hs))
      (mem_ball_zero_iff.2 (ht a))
    simpa [norm_div, div_le_iff₀ hn, Function.update_eq_self] using key
  have S₁ : ∀ t, (∀ i, ‖t i‖ < ρ) → ‖u (p t)‖ ≤ 1 / ρ * ‖t 0‖ := fun t ht => by
    simpa using hstep t 0 1 1 ht (by simp) fun s hs => by
      simpa using (hball _ (hpb _ fun i => by by_cases h : i = 0 <;> simp [h, hs, ht i])).2.1.le
  have S₂ : ∀ t, (∀ i, ‖t i‖ < ρ) → ‖u (p t)‖ ≤ 1 / ρ / ρ * ‖t 1‖ * ‖t 0‖ := fun t ht =>
    hstep t 1 (1 / ρ) (t 0) ht (hGz t 0 ht) fun s hs => by
      simpa using S₁ (Function.update t 1 s) (fun i => by by_cases h : i = 1 <;> simp [h, hs, ht i])
  have S₃ : ∀ t, (∀ i, ‖t i‖ < ρ) → ‖u (p t)‖ ≤ 1 / ρ / ρ / ρ * ‖t 2‖ * ‖t 1 * t 0‖ := fun t ht =>
    hstep t 2 (1 / ρ / ρ) (t 1 * t 0) ht (fun h => by
      rcases mul_eq_zero.1 h with h1 | h0
      · exact hGz t 1 ht h1
      · exact hGz t 0 ht h0) fun s hs => by
        simpa [norm_mul, mul_assoc] using S₂ (Function.update t 2 s)
          (fun i => by by_cases h : i = 2 <;> simp [h, hs, ht i])
  have hfin := S₃ (fun _ => 1) (fun _ => h1ρ)
  have hy1 : p (fun _ => 1) = y := by funext a; simp [p]
  rw [hy1] at hfin
  calc ‖u y‖ ≤ 1 / ρ / ρ / ρ := by simpa using hfin
    _ = 1 / R ^ 3 * ‖y‖ ^ 3 := by rw [hρdef]; field_simp

private lemma isBigO_norm_cube_comp_clm {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] {u : F' → ℂ}
    (hu : u =O[𝓝 0] fun z => ‖z‖ ^ 3) (T : E →L[ℂ] F') :
    (fun x => u (T x)) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
  refine (hu.comp_tendsto (by simpa using T.continuous.tendsto 0)).trans
    (IsBigO.of_bound (‖T‖ ^ 3) (Eventually.of_forall fun x => ?_))
  simpa only [Function.comp_apply, norm_pow, norm_norm, ← mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 3

theorem _root_.GlobalTheory.LocalCube.exists_third_difference :
    (∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧ ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ), F =O[𝓝 0] (fun z => ‖z‖ ^ 3) → (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  intro hA hB g F hF hF0 ⟨hax, heq⟩
  have hsign : ∑ I : Finset (Fin 3), ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) = 0 := by
    exact_mod_cast (by decide : ∑ I : Finset (Fin 3), (-1 : ℤ) ^ (3 - I.card) = 0)
  set L := Complex.log (F 0)
  have hL' : cexp L = F 0 := Complex.exp_log hF0
  set f : (Fin 3 → Fin g → ℂ) → ℂ := fun x => Complex.log (F x / F 0) with hfdef
  have hfa : AnalyticAt ℂ f 0 :=
    (hF.div analyticAt_const hF0).clog (by simp [hF0])
  have hFexp : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = cexp (L + f x) := by
    filter_upwards [hF.continuousAt.eventually_ne hF0] with x hx
    rw [Complex.exp_add, hL', hfdef, Complex.exp_log (div_ne_zero hx hF0), mul_div_cancel₀ _ hF0]
  have hfax : ∀ a, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → f x = 0 := fun a => by
    filter_upwards [hax a] with x hx h0
    simp only [hfdef, hx h0, div_self hF0, Complex.log_one]
  have hfO : f =O[𝓝 0] fun z => ‖z‖ ^ 3 := isBigO_norm_cube_of_analytic_vanishing_coords hfa hfax
  let M : (Fin g → ℂ) →L[ℂ] (Fin 3 → Fin g → ℂ) := ContinuousLinearMap.pi fun a : Fin 3 =>
    ![ContinuousLinearMap.id ℂ (Fin g → ℂ), ContinuousLinearMap.id ℂ (Fin g → ℂ),
      -ContinuousLinearMap.id ℂ (Fin g → ℂ)] a
  have hM : ∀ s, M s = ![s, s, -s] := fun s => by funext a; fin_cases a <;> simp [M]
  let S : Finset (Fin 3) → (Fin 3 → Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fun I =>
    ∑ a ∈ I, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Fin g → ℂ) a
  have hS : ∀ I x, S I x = ∑ a ∈ I, x a := fun I x => by simp [S]
  let φ : (Fin g → ℂ) → ℂ := fun s => f (M s)
  have hφa : AnalyticAt ℂ φ 0 := hfa.comp_of_eq (M.analyticAt 0) (map_zero M)
  have hφO : φ =O[𝓝 0] fun z => ‖z‖ ^ 3 := isBigO_norm_cube_comp_clm hfO M
  obtain ⟨k, hka, hkO, hkeq⟩ := hA g (fun s => -φ s) hφa.neg hφO.neg_left
  have hk0 : k 0 = 0 := (by simpa using hkO : k =O[𝓝 0] fun y => ‖y - 0‖ ^ 3).eq_zero_of_norm_pow (by norm_num)
  let D : ((Fin g → ℂ) → ℂ) → (Fin 3 → Fin g → ℂ) → ℂ := fun w x =>
    ∑ I : Finset (Fin 3), ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * w (∑ a ∈ I, x a)
  have hDO : ∀ w : (Fin g → ℂ) → ℂ, w =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      D w =O[𝓝 0] fun x => ‖x‖ ^ 3 := fun w hw => by
    have : D w = ∑ I : Finset (Fin 3), fun x => ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * w (S I x) := by
      funext x; simp [D, hS]
    rw [this]
    exact IsBigO.sum fun I _ => (isBigO_norm_cube_comp_clm hw (S I)).const_mul_left _
  let Gf : (Fin 3 → Fin g → ℂ) → ℂ := fun x => f x - D k x
  have ev2 : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) = cexp (L + f ((2 : ℂ) • x)) :=
    ((continuous_const_smul (2 : ℂ)).tendsto' 0 0 (smul_zero _)).eventually hFexp
  have evn : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F (-x) = cexp (L + f (-x)) :=
    (continuous_neg.tendsto' 0 0 neg_zero).eventually hFexp
  have evI : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3),
      F (M (∑ a ∈ I, x a)) = cexp (L + f (M (∑ a ∈ I, x a))) :=
    Filter.eventually_all.2 fun I => by
      simpa [hS] using ((M.comp (S I)).continuous.tendsto' 0 0 (map_zero _)).eventually hFexp
  have evk : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3),
      k ((2 : ℂ) • ∑ a ∈ I, x a) - 3 * k (∑ a ∈ I, x a) - k (-∑ a ∈ I, x a) = -φ (∑ a ∈ I, x a) :=
    Filter.eventually_all.2 fun I => by
      simpa [hS] using ((S I).continuous.tendsto' 0 0 (map_zero _)).eventually hkeq
  have hEt : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ),
      ‖f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x)‖ < 2 * π := by
    have hf0 : f 0 = 0 := (hfax 0).self_of_nhds rfl
    have hc : ContinuousAt (fun x : Fin 3 → Fin g → ℂ => f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x)) 0 := by
      have hc2 : ContinuousAt (fun x : Fin 3 → Fin g → ℂ => f ((2 : ℂ) • x)) 0 :=
        hfa.continuousAt.comp_of_eq (by fun_prop) (smul_zero _)
      have hcn : ContinuousAt (fun x : Fin 3 → Fin g → ℂ => f (-x)) 0 :=
        hfa.continuousAt.comp_of_eq continuous_neg.continuousAt neg_zero
      have hcD : ContinuousAt (D φ) 0 := tendsto_finsetSum _ fun I _ =>
        continuousAt_const.mul (hφa.continuousAt.comp_of_eq
          (continuous_finsetSum I fun a _ => continuous_apply a).continuousAt (by simp))
      exact ((hc2.add hcD).sub (continuousAt_const.mul hfa.continuousAt)).sub hcn
    exact hc.norm.eventually (gt_mem_nhds (by simp [D, φ, hf0]; positivity))
  have hE : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x) = 0 := by
    filter_upwards [heq, hFexp, ev2, evn, evI, hEt] with x hx hx1 hx2 hx3 hx4 hx5
    have hprod : ∏ I : Finset (Fin 3),
        F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card)) =
          cexp (D φ x) := by
      have hsum : ∑ I : Finset (Fin 3),
          ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * (L + φ (∑ a ∈ I, x a)) = D φ x := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsign, zero_mul, zero_add, D]
      rw [← hsum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun I _ => by rw [Complex.exp_intCast_mul, ← hM, hx4 I]
    rw [hprod, hx2, hx3, hx1, ← hL', ← Complex.exp_natCast_mul, ← Complex.exp_natCast_mul,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add] at hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hx
    have hEx : f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x) = n * (2 * π * Complex.I) := by
      linear_combination hn
    have h2 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left (by positivity : (0 : ℝ) < 2 * π)).1
      (by simpa [hEx, abs_of_pos Real.pi_pos] using hx5)
    have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h2)
    simp [hEx, hn0]
  have hGeq : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), Gf ((2 : ℂ) • x) = 3 * Gf x + Gf (-x) := by
    filter_upwards [hE, evk] with x hx hk
    have hD : D k ((2 : ℂ) • x) - 3 * D k x - D k (-x) = -D φ x := by
      simp only [D, Pi.smul_apply, Pi.neg_apply, ← Finset.smul_sum, Finset.sum_neg_distrib]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun I _ => ?_
      linear_combination ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * hk I
    show f ((2 : ℂ) • x) - D k ((2 : ℂ) • x) = 3 * (f x - D k x) + (f (-x) - D k (-x))
    linear_combination hx - hD
  refine ⟨k, hka, hk0, ?_⟩
  filter_upwards [hB (Fin 3 → Fin g → ℂ) Gf (hfO.sub (hDO k hkO)) hGeq, hFexp] with x hx hx1
  have hprod2 : ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card)) =
      cexp (D k x) := by
    simp only [D]
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun I _ => (Complex.exp_intCast_mul _ _).symm
  rw [hx1, ← hL', hprod2, ← Complex.exp_add]
  congr 1
  linear_combination (hx : f x - D k x = 0)

end GlobalTheory.LocalCube
