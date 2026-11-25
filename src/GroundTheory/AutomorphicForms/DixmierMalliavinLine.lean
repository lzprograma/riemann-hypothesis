module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function Complex
open scoped ContDiff FourierTransform

noncomputable section

/-! ### Elementary products, symmetric coefficients, and partial fractions -/

private lemma geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, r ^ k ≤ (1 - r)⁻¹ :=
  ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun _ _ => pow_nonneg hr0 _).trans_eq
    (tsum_geometric_of_lt_one hr0 hr1)

private def bN (lam : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | N + 1, m + 1 => bN lam N (m + 1) + (lam N)⁻¹ ^ 2 * bN lam N m

private lemma bN_zero_right (lam : ℕ → ℝ) (N : ℕ) : bN lam N 0 = 1 := by cases N <;> rfl

private lemma bN_eq_zero_of_lt (lam : ℕ → ℝ) : ∀ {N m : ℕ}, N < m → bN lam N m = 0
  | 0, _ + 1, _ => rfl
  | N + 1, m + 1, h => by
    simp [bN, bN_eq_zero_of_lt lam (by lia : N < m + 1), bN_eq_zero_of_lt lam (by lia : N < m)]

private lemma bN_nonneg (lam : ℕ → ℝ) : ∀ N m, 0 ≤ bN lam N m
  | 0, 0 => zero_le_one
  | 0, _ + 1 => le_rfl
  | _ + 1, 0 => zero_le_one
  | N + 1, m + 1 => add_nonneg (bN_nonneg lam N (m + 1)) (mul_nonneg (sq_nonneg _) (bN_nonneg lam N m))

private lemma bN_mono (lam : ℕ → ℝ) (N m : ℕ) : bN lam N m ≤ bN lam (N + 1) m := by
  cases m with
  | zero => simp [bN_zero_right]
  | succ m => exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (bN_nonneg lam N m))

private lemma bN_succ_eq_sum (lam : ℕ → ℝ) (N m : ℕ) :
    bN lam N (m + 1) = ∑ k ∈ Finset.range N, (lam k)⁻¹ ^ 2 * bN lam k m := by
  induction N with | zero => rfl | succ N ih => simp [bN, Finset.sum_range_succ, ih]

private def prodPoly (lam : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.range N, (1 + x / lam k ^ 2)

private lemma prodPoly_eq_sum (lam : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    prodPoly lam N x = ∑ m ∈ Finset.range (N + 1), bN lam N m * x ^ m := by
  induction N with
  | zero => simp [prodPoly, bN]
  | succ N ih =>
    rw [prodPoly, Finset.prod_range_succ, ← prodPoly, ih, mul_add, mul_one, Finset.sum_mul,
      Finset.sum_range_succ' (f := fun m => bN lam (N + 1) m * x ^ m), bN_zero_right, pow_zero,
      mul_one, Finset.sum_range_succ' (f := fun m => bN lam N m * x ^ m), bN_zero_right, pow_zero,
      mul_one, show ∑ k ∈ Finset.range (N + 1), bN lam N k * x ^ k * (x / lam N ^ 2) =
        ∑ k ∈ Finset.range (N + 1), ((lam N)⁻¹ ^ 2 * bN lam N k) * x ^ (k + 1) from
          Finset.sum_congr rfl fun _ _ => by rw [inv_pow, div_eq_mul_inv, pow_succ]; ring,
      Finset.sum_range_succ (f := fun k => ((lam N)⁻¹ ^ 2 * bN lam N k) * x ^ (k + 1)),
      Finset.sum_range_succ (f := fun k => bN lam (N + 1) (k + 1) * x ^ (k + 1))]
    simp only [bN, add_mul, Finset.sum_add_distrib, bN_eq_zero_of_lt lam (Nat.lt_succ_self N), zero_add]
    ring

private lemma one_le_prodPoly (lam : ℕ → ℝ) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ prodPoly lam N x :=
  Finset.one_le_prod₀ fun _ _ => le_add_of_nonneg_right (div_nonneg hx (sq_nonneg _))

private lemma prodPoly_mono (lam : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun N => prodPoly lam N x) :=
  monotone_nat_of_le_succ fun N => by
    change prodPoly lam N x ≤ prodPoly lam (N + 1) x
    rw [prodPoly, prodPoly, Finset.prod_range_succ]
    exact le_mul_of_one_le_right (le_trans zero_le_one (one_le_prodPoly lam N hx))
      (le_add_of_nonneg_right (div_nonneg hx (sq_nonneg _)))

private lemma prodPoly_le_exp {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : prodPoly lam N x ≤ Real.exp (x / 3) := by
  have h1 : prodPoly lam N x ≤ Real.exp (∑ k ∈ Finset.range N, x / lam k ^ 2) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => le_trans zero_le_one (le_add_of_nonneg_right
      (div_nonneg hx (sq_nonneg _)))) fun k _ => by linarith [Real.add_one_le_exp (x / lam k ^ 2)]
  refine h1.trans (Real.exp_le_exp.2 ?_)
  have h0 := geom_sum_le_inv_one_sub (r := 1 / 4) (by norm_num) (by norm_num) N
  calc ∑ k ∈ Finset.range N, x / lam k ^ 2
      ≤ ∑ k ∈ Finset.range N, x * (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ k := Finset.sum_le_sum fun k _ => by
        rw [div_eq_mul_inv, mul_assoc, ← pow_succ', one_div, inv_pow]
        refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hx
        calc (4 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ 2 := by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num
          _ ≤ lam k ^ 2 := by nlinarith [hlam k, show (0 : ℝ) < 2 ^ (k + 1) by positivity]
    _ = x * (1 / 4 : ℝ) * ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k := (Finset.mul_sum ..).symm
    _ ≤ x / 3 := by nlinarith

private lemma bN_le_two {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k) (N m : ℕ) :
    bN lam N m ≤ 2 := by
  by_cases hm : m ≤ N
  · have hexp : Real.exp (1 / 3 : ℝ) ≤ 2 := by
      have h := Real.add_one_le_exp (-1 / 3 : ℝ)
      rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring, Real.exp_neg,
        le_inv_comm₀ (by norm_num) (Real.exp_pos _)] at h
      linarith
    calc bN lam N m = bN lam N m * (1 : ℝ) ^ m := by simp
      _ ≤ prodPoly lam N 1 := by
          rw [prodPoly_eq_sum]
          exact Finset.single_le_sum (fun j _ => mul_nonneg (bN_nonneg lam N j) (by positivity))
            (Finset.mem_range.2 (by lia))
      _ ≤ 2 := (prodPoly_le_exp hlam N zero_le_one).trans hexp
  · rw [bN_eq_zero_of_lt lam (by lia)]; norm_num

private def bLim (lam : ℕ → ℝ) (m : ℕ) : ℝ := ⨆ N, bN lam N m

private lemma bddAbove_bN {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k) (m : ℕ) :
    BddAbove (Set.range fun N => bN lam N m) := ⟨2, by rintro _ ⟨N, rfl⟩; exact bN_le_two hlam N m⟩

private lemma tendsto_bN {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k) (m : ℕ) :
    Tendsto (fun N => bN lam N m) atTop (𝓝 (bLim lam m)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun N => bN_mono lam N m) (bddAbove_bN hlam m)

private lemma bN_le_bLim {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k) (N m : ℕ) :
    bN lam N m ≤ bLim lam m := le_ciSup (bddAbove_bN hlam m) N

private lemma bLim_zero (lam : ℕ → ℝ) : bLim lam 0 = 1 := by simp [bLim, bN_zero_right]

private lemma bLim_nonneg {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k) (m : ℕ) :
    0 ≤ bLim lam m := (bN_nonneg lam 0 m).trans (bN_le_bLim hlam 0 m)

private lemma exists_lam (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) :
    ∃ lam : ℕ → ℝ, 2 ≤ lam 0 ∧ (∀ k, 2 * lam k ≤ lam (k + 1)) ∧
      ∀ m, 1 ≤ m → bLim lam m ≤ δ m := by
  let u : ℕ → ℝ := fun k => (Finset.Icc 1 (k + 1)).inf' ⟨1, by simp⟩ δ
  have hu : ∀ k, 0 < u k := fun k => (Finset.lt_inf'_iff _).2 fun m _ => hδ m
  let lam : ℕ → ℝ := Nat.rec (max 2 (Real.sqrt (4 / u 0)))
    fun k prev => max (2 * prev) (Real.sqrt (4 * 2 ^ (k + 1) / u (k + 1)))
  have h0 : 2 ≤ lam 0 := le_max_left _ _
  have hstep : ∀ k, 2 * lam k ≤ lam (k + 1) := fun _ => le_max_left _ _
  have hpow : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k := fun k => by
    induction k with | zero => simpa using h0 | succ k ih => rw [pow_succ']; linarith [hstep k]
  refine ⟨lam, h0, hstep, fun m hm => ?_⟩
  cases m with
  | zero => lia
  | succ m =>
    refine ciSup_le fun N => ?_
    rw [bN_succ_eq_sum]
    have hgeo := geom_sum_le_inv_one_sub (r := 1 / 2) (by norm_num) (by norm_num) N
    norm_num at hgeo
    have hinv : ∀ k, m ≤ k → (lam k)⁻¹ ^ 2 ≤ δ (m + 1) / (4 * 2 ^ k) := fun k hk => by
      have hge : Real.sqrt (4 * 2 ^ k / u k) ≤ lam k := by
        cases k with | zero => simp [lam] | succ k => exact le_max_right _ _
      have hsq : 4 * 2 ^ k / u k ≤ lam k ^ 2 :=
        (Real.sq_sqrt (div_nonneg (by positivity) (hu k).le)).symm.trans_le
          (by nlinarith [Real.sqrt_nonneg (4 * 2 ^ k / u k)])
      have h1 : (lam k)⁻¹ ^ 2 ≤ u k / (4 * 2 ^ k) := by
        rw [inv_pow]; simpa [inv_div] using inv_anti₀ (div_pos (by positivity) (hu k)) hsq
      exact h1.trans <| div_le_div_of_nonneg_right
        (Finset.inf'_le δ (Finset.mem_Icc.2 ⟨by lia, by lia⟩)) (by positivity)
    calc ∑ k ∈ Finset.range N, (lam k)⁻¹ ^ 2 * bN lam k m
        ≤ ∑ k ∈ Finset.range N, (δ (m + 1) / 2) * (1 / 2 : ℝ) ^ k := Finset.sum_le_sum fun k _ => by
          by_cases hk : m ≤ k
          · calc (lam k)⁻¹ ^ 2 * bN lam k m ≤ (δ (m + 1) / (4 * 2 ^ k)) * 2 :=
                  mul_le_mul (hinv k hk) (bN_le_two hpow k m) (bN_nonneg lam k m)
                    (div_nonneg (hδ _).le (by positivity))
              _ = (δ (m + 1) / 2) * (1 / 2 : ℝ) ^ k := by rw [one_div, inv_pow]; ring
          · rw [bN_eq_zero_of_lt lam (by lia), mul_zero]
            exact mul_nonneg (div_nonneg (hδ _).le (by norm_num)) (by positivity)
      _ = (δ (m + 1) / 2) * ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k := (Finset.mul_sum ..).symm
      _ ≤ δ (m + 1) := by nlinarith [hδ (m + 1)]

private def infProd (lam : ℕ → ℝ) (x : ℝ) : ℝ := ∑' m, bLim lam m * x ^ m

private lemma summable_infProd {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    {x : ℝ} (hx : 0 ≤ x) : Summable (fun m => bLim lam m * x ^ m) :=
  summable_of_sum_range_le (c := Real.exp (x / 3))
    (fun m => mul_nonneg (bLim_nonneg hlam m) (pow_nonneg hx m)) fun M =>
    le_of_tendsto (tendsto_finsetSum _ fun m _ => (tendsto_bN hlam m).mul_const _)
      (eventually_atTop.2 ⟨M, fun N hN =>
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by lia))
          fun m _ _ => mul_nonneg (bN_nonneg lam N m) (pow_nonneg hx m)).trans
          ((prodPoly_eq_sum lam N x).symm.trans_le (prodPoly_le_exp hlam N hx))⟩)

private lemma prodPoly_le_infProd {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : prodPoly lam N x ≤ infProd lam x := by
  rw [prodPoly_eq_sum]
  exact (Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right (bN_le_bLim hlam N m)
    (pow_nonneg hx m)).trans ((summable_infProd hlam hx).sum_le_tsum _ fun m _ =>
      mul_nonneg (bLim_nonneg hlam m) (pow_nonneg hx m))

private lemma tendsto_prodPoly {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    {x : ℝ} (hx : 0 ≤ x) : Tendsto (fun N => prodPoly lam N x) atTop (𝓝 (infProd lam x)) := by
  have hbdd : BddAbove (Set.range fun N => prodPoly lam N x) :=
    ⟨infProd lam x, by rintro _ ⟨N, rfl⟩; exact prodPoly_le_infProd hlam N hx⟩
  suffices (⨆ N, prodPoly lam N x) = infProd lam x by
    rw [← this]; exact tendsto_atTop_ciSup (prodPoly_mono lam hx) hbdd
  refine le_antisymm (ciSup_le fun N => prodPoly_le_infProd hlam N hx) <|
    le_of_tendsto (summable_infProd hlam hx).hasSum.tendsto_sum_nat (Eventually.of_forall fun M =>
      le_of_tendsto (tendsto_finsetSum _ fun m _ => (tendsto_bN hlam m).mul_const _)
        (eventually_atTop.2 ⟨M, fun N hN =>
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by lia))
            fun m _ _ => mul_nonneg (bN_nonneg lam N m) (pow_nonneg hx m)).trans
            ((prodPoly_eq_sum lam N x).symm.trans_le (le_ciSup hbdd N))⟩))

private lemma one_le_infProd {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    {x : ℝ} (hx : 0 ≤ x) : 1 ≤ infProd lam x :=
  (one_le_prodPoly lam 0 hx).trans (prodPoly_le_infProd hlam 0 hx)

private lemma continuous_prodPoly (lam : ℕ → ℝ) (N : ℕ) :
    Continuous (fun ξ : ℝ => prodPoly lam N ((2 * π * ξ) ^ 2)) :=
  continuous_finsetProd _ fun _ _ => by fun_prop

private lemma measurable_infProd {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k) :
    Measurable (fun ξ : ℝ => infProd lam ((2 * π * ξ) ^ 2)) :=
  measurable_of_tendsto_metrizable (fun N => (continuous_prodPoly lam N).measurable)
    (tendsto_pi_nhds.2 fun _ => tendsto_prodPoly hlam (sq_nonneg _))

private def pfCoeff (lam : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∏ j ∈ (Finset.range N).erase k, (1 - (lam k / lam j) ^ 2)⁻¹

private lemma two_factor_pf {a b x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h1 : 1 + x / a ≠ 0)
    (h2 : 1 + x / b ≠ 0) (h3 : 1 - a / b ≠ 0) :
    (1 + x / a)⁻¹ * (1 + x / b)⁻¹ =
      (1 - a / b)⁻¹ * (1 + x / a)⁻¹ + (1 - b / a)⁻¹ * (1 + x / b)⁻¹ := by
  have h1' : a + x ≠ 0 := fun h => h1 (by field_simp; linarith)
  have h2' : b + x ≠ 0 := fun h => h2 (by field_simp; linarith)
  have h3' : b - a ≠ 0 := fun h => h3 (by field_simp; linarith)
  have h4' : a - b ≠ 0 := fun h => h3' (by linarith)
  field_simp; ring

private lemma inv_prodPoly_eq_sum {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k) (hmono : StrictMono lam) :
    ∀ {N : ℕ}, 1 ≤ N → ∀ {x : ℝ}, (∀ k < N, 1 + x / lam k ^ 2 ≠ 0) →
      (prodPoly lam N x)⁻¹ = ∑ k ∈ Finset.range N, pfCoeff lam N k * (1 + x / lam k ^ 2)⁻¹ := by
  intro N hN; induction N with
  | zero => lia
  | succ N ih =>
    intro x hx; cases N with
    | zero => simp [prodPoly, pfCoeff]
    | succ M =>
      set N := M + 1
      have hne_sq : ∀ {j k : ℕ}, j ≠ k → 1 - (lam j / lam k) ^ 2 ≠ 0 := fun {j k} hjk h =>
        hjk <| hmono.injective <| (div_eq_one_iff_eq (hpos k).ne').1
          (by nlinarith [div_pos (hpos j) (hpos k), sq_eq_one_iff.1 (by linarith : (lam j / lam k) ^ 2 = 1)])
      have hpf_step : ∀ k < N, pfCoeff lam (N + 1) k = pfCoeff lam N k * (1 - (lam k / lam N) ^ 2)⁻¹ :=
        fun k hk => by
          have herase : (Finset.range (N + 1)).erase k = insert N ((Finset.range N).erase k) := by
            ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]; lia
          rw [pfCoeff, herase, Finset.prod_insert (by simp), mul_comm]; rfl
      have hpf_last : pfCoeff lam (N + 1) N = (prodPoly lam N (-(lam N ^ 2)))⁻¹ := by
        rw [pfCoeff, prodPoly, Finset.range_add_one, Finset.erase_insert (by simp), ← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun _ _ => by congr 1; rw [div_pow]; ring
      rw [prodPoly, Finset.prod_range_succ, ← prodPoly, mul_inv,
        ih (by lia) (fun k hk => hx k (by lia)), Finset.sum_mul, Finset.sum_range_succ (n := N)]
      calc ∑ k ∈ Finset.range N, pfCoeff lam N k * (1 + x / lam k ^ 2)⁻¹ * (1 + x / lam N ^ 2)⁻¹
          = ∑ k ∈ Finset.range N, (pfCoeff lam (N + 1) k * (1 + x / lam k ^ 2)⁻¹ +
              pfCoeff lam N k * (1 - (lam N / lam k) ^ 2)⁻¹ * (1 + x / lam N ^ 2)⁻¹) :=
            Finset.sum_congr rfl fun k hk => by
              have hkl : k < N := Finset.mem_range.1 hk
              have h2 := two_factor_pf (pow_ne_zero 2 (hpos k).ne') (pow_ne_zero 2 (hpos N).ne')
                (hx k (by lia)) (hx N (by lia)) (by rw [← div_pow]; exact hne_sq (by lia))
              rw [← div_pow, ← div_pow] at h2
              rw [mul_assoc, h2, mul_add, hpf_step k hkl]; ring
        _ = (∑ k ∈ Finset.range N, pfCoeff lam (N + 1) k * (1 + x / lam k ^ 2)⁻¹) +
            (∑ k ∈ Finset.range N, pfCoeff lam N k * (1 + (-(lam N ^ 2)) / lam k ^ 2)⁻¹) *
              (1 + x / lam N ^ 2)⁻¹ := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
            congr 1; exact Finset.sum_congr rfl fun _ _ => by congr 2; rw [div_pow]; ring
        _ = (∑ k ∈ Finset.range N, pfCoeff lam (N + 1) k * (1 + x / lam k ^ 2)⁻¹) +
            pfCoeff lam (N + 1) N * (1 + x / lam N ^ 2)⁻¹ := by
            rw [← ih (by lia) (fun k hk => by
              rw [show 1 + -(lam N ^ 2) / lam k ^ 2 = 1 - (lam N / lam k) ^ 2 by rw [div_pow]; ring]
              exact hne_sq (by lia)), hpf_last]

private lemma one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) : 1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 := (hu a (Finset.mem_insert_self a s)).1
    have ha1 := (hu a (Finset.mem_insert_self a s)).2
    have ih' := ih fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg fun i hi => (hu i (Finset.mem_insert_of_mem hi)).1
    nlinarith

private lemma lam_ratio_le {lam : ℕ → ℝ} (hstep : ∀ k, 2 * lam k ≤ lam (k + 1)) :
    ∀ {j k : ℕ}, j ≤ k → (2 : ℝ) ^ (k - j) * lam j ≤ lam k := by
  intro j k hjk; induction k with
  | zero =>
    obtain rfl : j = 0 := by lia
    simp
  | succ k ih =>
    rcases eq_or_lt_of_le hjk with rfl | hlt
    · simp
    · rw [show k + 1 - j = (k - j) + 1 by lia, pow_succ, mul_comm ((2 : ℝ) ^ (k - j)) 2, mul_assoc]
      exact (mul_le_mul_of_nonneg_left (ih (by lia)) (by positivity)).trans (hstep k)

private lemma abs_pfCoeff_le {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k)
    (hstep : ∀ k, 2 * lam k ≤ lam (k + 1)) {N k : ℕ} (hk : k < N) :
    |pfCoeff lam N k| ≤ 2 * (1 / 3 : ℝ) ^ k := by
  have hunion : (Finset.range N).erase k = Finset.range k ∪ Finset.Ico (k + 1) N := by
    ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; lia
  have hdisj : Disjoint (Finset.range k) (Finset.Ico (k + 1) N) :=
    Finset.disjoint_left.2 fun _ h1 h2 => by simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; lia
  rw [pfCoeff, hunion, Finset.prod_union hdisj, abs_mul, mul_comm (2 : ℝ)]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
  · rw [Finset.abs_prod]
    calc ∏ j ∈ Finset.range k, |(1 - (lam k / lam j) ^ 2)⁻¹|
        ≤ ∏ _j ∈ Finset.range k, (1 / 3 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j hj => by
          have h2 : 2 * lam j ≤ lam k := (hstep j).trans <|
            (le_mul_of_one_le_left (hpos _).le (one_le_pow₀ (by norm_num))).trans
              (lam_ratio_le hstep (by simp only [Finset.mem_range] at hj; lia))
          have hdiv : 2 ≤ lam k / lam j := (le_div_iff₀ (hpos j)).2 h2
          rw [abs_inv, abs_of_neg (by nlinarith : 1 - (lam k / lam j) ^ 2 < 0), one_div]
          exact inv_anti₀ (by norm_num) (by nlinarith)
      _ = (1 / 3 : ℝ) ^ k := by simp
  · have hu : ∀ j ∈ Finset.Ico (k + 1) N,
        0 ≤ (lam k / lam j) ^ 2 ∧ (lam k / lam j) ^ 2 ≤ (1 / 4 : ℝ) ^ (j - k) := fun j hj => by
      have hdiv : lam k / lam j ≤ (1 / 2 : ℝ) ^ (j - k) := by
        rw [div_le_iff₀ (hpos j), one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
        linarith [lam_ratio_le hstep (by simp only [Finset.mem_Ico] at hj; lia : k ≤ j)]
      refine ⟨sq_nonneg _, ?_⟩
      calc (lam k / lam j) ^ 2 ≤ ((1 / 2 : ℝ) ^ (j - k)) ^ 2 := by
            nlinarith [div_nonneg (hpos k).le (hpos j).le]
        _ = (1 / 4 : ℝ) ^ (j - k) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hprod_ge : (1 / 2 : ℝ) ≤ ∏ j ∈ Finset.Ico (k + 1) N, (1 - (lam k / lam j) ^ 2) := by
      have h1 := one_sub_sum_le_prod (Finset.Ico (k + 1) N) (fun j => (lam k / lam j) ^ 2)
        fun j hj => ⟨(hu j hj).1, (hu j hj).2.trans (pow_le_one₀ (by norm_num) (by norm_num))⟩
      have hgeom := geom_sum_le_inv_one_sub (r := 1 / 4) (by norm_num) (by norm_num) (N - (k + 1))
      have hsum : ∑ j ∈ Finset.Ico (k + 1) N, (lam k / lam j) ^ 2 ≤ 1 / 3 := by
        calc ∑ j ∈ Finset.Ico (k + 1) N, (lam k / lam j) ^ 2
            ≤ ∑ j ∈ Finset.Ico (k + 1) N, (1 / 4 : ℝ) ^ (j - k) :=
              Finset.sum_le_sum fun j hj => (hu j hj).2
          _ = ∑ i ∈ Finset.range (N - (k + 1)), (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ i := by
              rw [Finset.sum_Ico_eq_sum_range]
              exact Finset.sum_congr rfl fun i _ => by rw [show k + 1 + i - k = i + 1 by lia, pow_succ']
          _ ≤ 1 / 3 := by rw [← Finset.mul_sum]; linarith
      linarith
    rw [Finset.prod_inv_distrib, abs_inv, abs_of_pos (lt_of_lt_of_le (by norm_num) hprod_ge)]
    linarith [inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hprod_ge]

/-! ### Fourier transform of `e^{-a|t|}` and fundamental solution `fundSol` -/

private lemma integrable_inv_one_add_div_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun ξ : ℝ => (((1 + (2 * π * ξ / a) ^ 2)⁻¹ : ℝ) : ℂ)) :=
  ((integrable_inv_one_add_sq.comp_mul_left' (by positivity : 2 * π / a ≠ 0)).ofReal (𝕜 := ℂ)).congr
    (Eventually.of_forall fun ξ => by
      show (((1 + (2 * π / a * ξ) ^ 2)⁻¹ : ℝ) : ℂ) = _
      rw [show 2 * π / a * ξ = 2 * π * ξ / a by ring])

private lemma fourierInv_inv_one_add_sq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ∫ ξ : ℝ, (((1 + (2 * π * ξ / a) ^ 2)⁻¹ : ℝ) : ℂ) * Complex.exp (↑(2 * π * t * ξ) * I) =
      ((a / 2 * Real.exp (-a * |t|) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun s => ((a / 2 * Real.exp (-a * |s|) : ℝ) : ℂ)
  have hf_int : Integrable f := integrableOn_univ.1 <| by
    rw [← Set.union_compl_self (Iic 0)]
    refine integrableOn_union.2 ⟨IntegrableOn.congr_fun
      (((integrableOn_exp_mul_Iic ha 0).const_mul (a / 2)).ofReal)
      (fun s hs => by simp [f, abs_of_nonpos (hs : s ≤ 0)]) measurableSet_Iic, ?_⟩
    rw [compl_Iic]
    exact IntegrableOn.congr_fun (((integrableOn_exp_mul_Ioi (neg_lt_zero.2 ha) 0).const_mul (a / 2)).ofReal)
      (fun s hs => by simp [f, abs_of_pos (hs : 0 < s)]) measurableSet_Ioi
  have hFf_eq : 𝓕 f = fun ξ : ℝ => (((1 + (2 * π * ξ / a) ^ 2)⁻¹ : ℝ) : ℂ) := funext fun ξ => by
    rw [Real.fourier_eq']
    have hre_neg : ((-(a : ℂ) - (2 * π * ξ : ℝ) * I)).re < 0 := by simp [ha]
    have hre_pos : 0 < ((a : ℂ) - (2 * π * ξ : ℝ) * I).re := by simp [ha]
    have hIic_eq : EqOn (fun s : ℝ => Complex.exp (↑(-2 * π * inner ℝ s ξ) * I) • f s)
        (fun s : ℝ => ((a / 2 : ℝ) : ℂ) * Complex.exp (((a : ℂ) - (2 * π * ξ : ℝ) * I) * (s : ℂ)))
        (Iic 0) := fun s hs => by
      simp only [f, smul_eq_mul, RCLike.inner_apply, conj_trivial, abs_of_nonpos (hs : s ≤ 0),
        Complex.ofReal_mul, Complex.ofReal_exp]
      rw [mul_comm, mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    have hIoi_eq : EqOn (fun s : ℝ => Complex.exp (↑(-2 * π * inner ℝ s ξ) * I) • f s)
        (fun s : ℝ => ((a / 2 : ℝ) : ℂ) * Complex.exp ((-(a : ℂ) - (2 * π * ξ : ℝ) * I) * (s : ℂ)))
        (Ioi 0) := fun s hs => by
      simp only [f, smul_eq_mul, RCLike.inner_apply, conj_trivial, abs_of_pos (hs : 0 < s),
        Complex.ofReal_mul, Complex.ofReal_exp]
      rw [mul_comm, mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    have hint : Integrable (fun s : ℝ => Complex.exp (↑(-2 * π * inner ℝ s ξ) * I) • f s) :=
      integrableOn_univ.1 <| by
        rw [← Set.union_compl_self (Iic 0)]
        refine integrableOn_union.2
          ⟨IntegrableOn.congr_fun ((integrableOn_exp_mul_complex_Iic hre_pos 0).const_mul _)
            hIic_eq.symm measurableSet_Iic, ?_⟩
        rw [compl_Iic]
        exact IntegrableOn.congr_fun ((integrableOn_exp_mul_complex_Ioi hre_neg 0).const_mul _)
          hIoi_eq.symm measurableSet_Ioi
    rw [← integral_add_compl measurableSet_Iic hint, setIntegral_congr_fun measurableSet_Iic hIic_eq,
      compl_Iic, setIntegral_congr_fun measurableSet_Ioi hIoi_eq, integral_const_mul,
      integral_const_mul, integral_exp_mul_complex_Iic hre_pos 0,
      integral_exp_mul_complex_Ioi hre_neg 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hre : ∀ c : ℝ, c ≠ 0 → (c : ℂ) - 2 * π * ξ * I ≠ 0 := fun c hc h =>
      hc (by simpa using congrArg Complex.re h)
    have hden2 : (a : ℂ) ^ 2 + (2 * π * ξ : ℂ) ^ 2 ≠ 0 := by
      rw [show (a : ℂ) ^ 2 + (2 * π * ξ : ℂ) ^ 2 = (((a ^ 2 + (2 * π * ξ) ^ 2 : ℝ) : ℂ)) by push_cast; ring]
      exact_mod_cast (by positivity : (0 : ℝ) < a ^ 2 + (2 * π * ξ) ^ 2).ne'
    have hden : (1 : ℂ) + ((2 * π * ξ : ℂ) / (a : ℂ)) ^ 2 ≠ 0 := by
      rw [show (1 : ℂ) + ((2 * π * ξ : ℂ) / (a : ℂ)) ^ 2 = (((1 + (2 * π * ξ / a) ^ 2 : ℝ) : ℂ)) by push_cast; ring]
      exact_mod_cast (by positivity : (0 : ℝ) < 1 + (2 * π * ξ / a) ^ 2).ne'
    have hprod : ((a : ℂ) - 2 * π * ξ * I) * (-(a : ℂ) - 2 * π * ξ * I) =
        -((a : ℂ) ^ 2 + (2 * π * ξ : ℂ) ^ 2) := by
      calc ((a : ℂ) - 2 * π * ξ * I) * (-(a : ℂ) - 2 * π * ξ * I)
          = -(a : ℂ) ^ 2 + (2 * π * ξ : ℂ) ^ 2 * I ^ 2 := by ring
        _ = -((a : ℂ) ^ 2 + (2 * π * ξ : ℂ) ^ 2) := by rw [Complex.I_sq]; ring
    push_cast
    rw [← mul_add, div_add_div _ _ (by simpa [mul_assoc] using hre a ha.ne')
      (by simpa [mul_assoc] using hre (-a) (neg_ne_zero.2 ha.ne')),
      show ((a : ℂ) - 2 * ↑π * ↑ξ * I) * (-↑a - 2 * ↑π * ↑ξ * I) =
        -((a : ℂ) ^ 2 + (2 * π * ξ : ℂ) ^ 2) by simpa [mul_assoc] using hprod]
    field_simp [(by exact_mod_cast ha.ne' : (a : ℂ) ≠ 0), hden, hden2]; ring
  have hFf_int : Integrable (𝓕 f) := by rw [hFf_eq]; exact integrable_inv_one_add_div_sq ha
  have hinv := congrFun ((by fun_prop : Continuous f).fourierInv_fourier_eq hf_int hFf_int) t
  rw [hFf_eq, Real.fourierInv_eq'] at hinv
  change _ = f t; rw [← hinv]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  rw [mul_comm _ (Complex.exp _), mul_assoc (2 * π)]

private lemma fourierInv_eq_integral (f : ℝ → ℂ) :
    (fun s : ℝ => ∫ ξ : ℝ, f ξ * Complex.exp (↑(2 * π * s * ξ) * I)) = 𝓕 (fun x => f (-x)) := by
  ext s
  rw [← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  rw [mul_comm _ (Complex.exp _), mul_assoc (2 * π), mul_comm s ξ]

private lemma integrable_pow_smul_comp_neg {f : ℝ → ℂ} {k : ℕ}
    (h : Integrable (fun ξ : ℝ => (2 * π * I * ξ) ^ k * f ξ)) :
    Integrable (fun x : ℝ => x ^ k • f (-x)) := by
  have hc : (-2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine (h.comp_neg.const_mul (((-2 * π * I : ℂ) ^ k)⁻¹)).congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [show (2 * π * I * ((-x : ℝ) : ℂ)) ^ k = (-2 * π * I : ℂ) ^ k * (x : ℂ) ^ k by
      rw [← mul_pow]; congr 1; push_cast; ring,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hc), one_mul,
    Complex.real_smul, Complex.ofReal_pow]

private lemma iteratedDeriv_fourierInv_eq {f : ℝ → ℂ} {n : ℕ}
    (hf : ∀ k ≤ n, Integrable (fun ξ : ℝ => (2 * π * I * ξ) ^ k * f ξ)) :
    ∀ k ≤ n, iteratedDeriv k (fun s : ℝ => ∫ ξ : ℝ, f ξ * Complex.exp (↑(2 * π * s * ξ) * I)) =
      fun t => ∫ ξ : ℝ, (2 * π * I * ξ) ^ k * f ξ * Complex.exp (↑(2 * π * t * ξ) * I) := by
  intro k hk
  rw [fourierInv_eq_integral, Real.iteratedDeriv_fourier (N := (k : ℕ∞))
    (fun m hm => integrable_pow_smul_comp_neg (hf m ((WithTop.coe_le_coe.1 hm).trans hk))) le_rfl]
  ext t
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [neg_neg, smul_eq_mul]
  rw [show (-2 * π * I * ((-ξ : ℝ) : ℂ)) ^ k = (2 * π * I * (ξ : ℂ)) ^ k by congr 1; push_cast; ring,
    show ((-2 * π * (-ξ) * t : ℝ) : ℂ) = ↑(2 * π * t * ξ) by push_cast; ring,
    mul_comm (Complex.exp _)]

private lemma contDiff_fourierInv {f : ℝ → ℂ}
    (hf : ∀ k : ℕ, Integrable (fun ξ : ℝ => (2 * π * I * ξ) ^ k * f ξ)) :
    ContDiff ℝ ∞ (fun s : ℝ => ∫ ξ : ℝ, f ξ * Complex.exp (↑(2 * π * s * ξ) * I)) := by
  rw [fourierInv_eq_integral]
  refine Real.contDiff_fourier fun k _ => ?_
  simpa only [norm_smul, norm_pow] using (integrable_pow_smul_comp_neg (hf k)).norm

private lemma integrable_pow_div_prodPoly {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k)
    (hmono : Monotone lam) {k N : ℕ} (hkN : k + 1 ≤ N) :
    Integrable (fun ξ : ℝ => (2 * π * I * ξ) ^ k * (((prodPoly lam N ((2 * π * ξ) ^ 2))⁻¹ : ℝ) : ℂ)) := by
  have hlk := hpos k
  have hdom : Integrable (fun ξ : ℝ => lam k ^ k * (1 + (2 * π * ξ / lam k) ^ 2)⁻¹) :=
    ((integrable_inv_one_add_sq.comp_mul_left' (by positivity : 2 * π / lam k ≠ 0)).const_mul
      (lam k ^ k)).congr
      (Eventually.of_forall fun ξ => by dsimp only; rw [show 2 * π / lam k * ξ = 2 * π * ξ / lam k by ring])
  refine hdom.mono'
    (((by fun_prop : Continuous fun ξ : ℝ => (2 * π * I * ξ) ^ k).mul
      (Complex.continuous_ofReal.comp ((continuous_prodPoly lam N).inv₀ fun ξ =>
        (lt_of_lt_of_le zero_lt_one (one_le_prodPoly lam N (sq_nonneg _))).ne')))).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  set y : ℝ := |2 * π * ξ| / lam k
  have hy : 0 ≤ y := div_nonneg (abs_nonneg _) hlk.le
  have hy2 : y ^ 2 = (2 * π * ξ / lam k) ^ 2 := by rw [div_pow, sq_abs, div_pow]
  have hPpos : 0 < prodPoly lam N ((2 * π * ξ) ^ 2) :=
    lt_of_lt_of_le zero_lt_one (one_le_prodPoly lam N (sq_nonneg _))
  have hP_ge : (1 + y ^ 2) ^ (k + 1) ≤ prodPoly lam N ((2 * π * ξ) ^ 2) := by
    calc (1 + y ^ 2) ^ (k + 1)
        = ∏ _j ∈ Finset.range (k + 1), (1 + (2 * π * ξ) ^ 2 / lam k ^ 2) := by
          rw [hy2, div_pow, Finset.prod_const, Finset.card_range]
      _ ≤ prodPoly lam (k + 1) ((2 * π * ξ) ^ 2) :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j hj => by
            have hjk : lam j ≤ lam k := hmono (by simp only [Finset.mem_range] at hj; lia)
            have hsq : lam j ^ 2 ≤ lam k ^ 2 := by nlinarith [hpos j]
            linarith [div_le_div_of_nonneg_left (sq_nonneg (2 * π * ξ)) (pow_pos (hpos j) 2) hsq]
      _ ≤ prodPoly lam N ((2 * π * ξ) ^ 2) := prodPoly_mono lam (sq_nonneg _) hkN
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hPpos),
    show (2 * π * I * ξ : ℂ) = ((2 * π * ξ : ℝ) : ℂ) * I by push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    ← div_eq_mul_inv, ← hy2, ← div_eq_mul_inv]
  have h1 : y ^ k ≤ (1 + y ^ 2) ^ k := pow_le_pow_left₀ hy (by nlinarith [sq_nonneg (y - 1)]) k
  calc |2 * π * ξ| ^ k / prodPoly lam N ((2 * π * ξ) ^ 2)
      ≤ |2 * π * ξ| ^ k / (1 + y ^ 2) ^ (k + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hP_ge
    _ = lam k ^ k * (y ^ k / (1 + y ^ 2) ^ k) / (1 + y ^ 2) := by
        rw [show |2 * π * ξ| ^ k = lam k ^ k * y ^ k by
          dsimp only [y]; rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero k hlk.ne')], pow_succ]
        field_simp [hlk.ne', (by positivity : (1 + y ^ 2 : ℝ) ≠ 0)]
    _ ≤ lam k ^ k / (1 + y ^ 2) := by
        calc lam k ^ k * (y ^ k / (1 + y ^ 2) ^ k) / (1 + y ^ 2)
            ≤ lam k ^ k * 1 / (1 + y ^ 2) := by gcongr; exact (div_le_one (by positivity)).2 h1
          _ = lam k ^ k / (1 + y ^ 2) := by rw [mul_one]

private lemma integrable_pow_div_infProd {lam : ℕ → ℝ}
    (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k) (hmono : Monotone lam) (k : ℕ) :
    Integrable (fun ξ : ℝ => (2 * π * I * ξ) ^ k * (((infProd lam ((2 * π * ξ) ^ 2))⁻¹ : ℝ) : ℂ)) := by
  have hpos : ∀ j, 0 < lam j := fun j => lt_of_lt_of_le (by positivity) (hlam j)
  refine (integrable_pow_div_prodPoly hpos hmono (le_refl (k + 1))).norm.mono'
    (((by fun_prop : Continuous fun ξ : ℝ => (2 * π * I * ξ) ^ k).measurable.mul
      (Complex.continuous_ofReal.measurable.comp (measurable_infProd hlam).inv))).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : 0 < prodPoly lam (k + 1) ((2 * π * ξ) ^ 2) :=
    lt_of_lt_of_le zero_lt_one (one_le_prodPoly lam (k + 1) (sq_nonneg _))
  have h2 := prodPoly_le_infProd hlam (k + 1) (sq_nonneg (2 * π * ξ))
  rw [abs_of_pos (inv_pos.2 (h1.trans_le h2)), abs_of_pos (inv_pos.2 h1)]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ h1 h2) (norm_nonneg _)

private lemma iteratedDeriv_cexp_const_mul (c : ℂ) (q : ℕ) :
    iteratedDeriv q (fun s : ℝ => Complex.exp (c * (s : ℂ))) =
      fun s : ℝ => c ^ q * Complex.exp (c * (s : ℂ)) := by
  induction q with
  | zero => funext s; simp
  | succ q ih =>
    rw [iteratedDeriv_succ, ih]; funext s
    have h1 : HasDerivAt (fun u : ℝ => c * (u : ℂ)) c s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul c
    exact (by convert (h1.cexp).const_mul (c ^ q) using 1; rw [pow_succ]; ring :
      HasDerivAt (fun u : ℝ => c ^ q * Complex.exp (c * (u : ℂ)))
        (c ^ (q + 1) * Complex.exp (c * (s : ℂ))) s).deriv

private lemma iteratedDeriv_exp_neg_abs_norm {a t : ℝ} (ha : 0 < a) (ht : t ≠ 0) (q : ℕ) :
    ‖iteratedDeriv q (fun s : ℝ => ((a / 2 * Real.exp (-a * |s|) : ℝ) : ℂ)) t‖ =
      a ^ (q + 1) * Real.exp (-a * |t|) / 2 := by
  have hsign : ∃ σ : ℝ, |σ| = 1 ∧ σ * t = -|t| ∧
      (fun s : ℝ => ((a / 2 * Real.exp (-a * |s|) : ℝ) : ℂ)) =ᶠ[𝓝 t]
        fun s : ℝ => ((a / 2 : ℝ) : ℂ) * Complex.exp ((σ * a : ℝ) * (s : ℂ)) := by
    rcases lt_or_gt_of_ne ht with h | h
    · refine ⟨1, by simp, by simp [abs_of_neg h], ?_⟩
      filter_upwards [Iio_mem_nhds h] with s hs; simp [abs_of_neg (hs : s < 0), Complex.ofReal_exp]
    · refine ⟨-1, by simp, by simp [abs_of_pos h], ?_⟩
      filter_upwards [Ioi_mem_nhds h] with s hs; simp [abs_of_pos (hs : 0 < s), Complex.ofReal_exp]
  rcases hsign with ⟨σ, hσ, hσt, hev⟩
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const_mul_field,
    congrFun (iteratedDeriv_cexp_const_mul ((σ * a : ℝ) : ℂ) q) t, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (div_pos ha two_pos), abs_mul, hσ, one_mul, abs_of_pos ha,
    ← Complex.ofReal_mul, Complex.norm_exp_ofReal,
    show σ * a * t = -a * |t| by rw [mul_comm σ a, mul_assoc, hσt]; ring, pow_succ']
  ring

private def Dbound (ε : ℝ) (q : ℕ) : ℝ :=
  (3 / 2 : ℝ) * (q + 1).factorial * (2 / ε) ^ (q + 1)

private def fundSol (lam : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∫ ξ : ℝ, (((infProd lam ((2 * π * ξ) ^ 2))⁻¹ : ℝ) : ℂ) * Complex.exp (↑(2 * π * t * ξ) * I)

private lemma contDiff_fundSol {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    (hmono : Monotone lam) : ContDiff ℝ ∞ (fundSol lam) :=
  contDiff_fourierInv (integrable_pow_div_infProd hlam hmono)

private lemma iteratedDeriv_fundSol {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    (hmono : Monotone lam) (q : ℕ) (t : ℝ) :
    iteratedDeriv q (fundSol lam) t =
      ∫ ξ : ℝ, (2 * π * I * ξ) ^ q * (((infProd lam ((2 * π * ξ) ^ 2))⁻¹ : ℝ) : ℂ) *
        Complex.exp (↑(2 * π * t * ξ) * I) :=
  congrFun (iteratedDeriv_fourierInv_eq (fun k _ => integrable_pow_div_infProd hlam hmono k) q le_rfl) t

private lemma norm_iteratedDeriv_fundSol_le {lam : ℕ → ℝ} (hlam0 : 2 ≤ lam 0)
    (hstep : ∀ k, 2 * lam k ≤ lam (k + 1)) {ε : ℝ} (hε : 0 < ε) (q : ℕ) {t : ℝ}
    (ht : ε / 2 ≤ |t|) : ‖iteratedDeriv q (fundSol lam) t‖ ≤ Dbound ε q := by
  have hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k := fun k => by
    induction k with | zero => simpa using hlam0 | succ k ih => rw [pow_succ']; linarith [hstep k]
  have hpos : ∀ k, 0 < lam k := fun k => lt_of_lt_of_le (by positivity) (hlam k)
  have hmono : StrictMono lam := strictMono_nat_of_lt_succ fun k => by linarith [hpos k, hstep k]
  have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
  let EN : ℕ → ℝ → ℂ := fun N s =>
    ∫ ξ : ℝ, (((prodPoly lam N ((2 * π * ξ) ^ 2))⁻¹ : ℝ) : ℂ) * Complex.exp (↑(2 * π * s * ξ) * I)
  have hEN_eq : ∀ N ≥ 1, EN N = fun s =>
      ∑ k ∈ Finset.range N, (pfCoeff lam N k : ℂ) * ((lam k / 2 * Real.exp (-lam k * |s|) : ℝ) : ℂ) := by
    intro N hN; funext s; dsimp [EN]
    rw [show (fun ξ : ℝ => (((prodPoly lam N ((2 * π * ξ) ^ 2))⁻¹ : ℝ) : ℂ) *
          Complex.exp (↑(2 * π * s * ξ) * I)) =
        fun ξ : ℝ => ∑ k ∈ Finset.range N, (pfCoeff lam N k : ℂ) *
          ((((1 + (2 * π * ξ / lam k) ^ 2)⁻¹ : ℝ) : ℂ) * Complex.exp (↑(2 * π * s * ξ) * I)) from
      funext fun ξ => by
        rw [inv_prodPoly_eq_sum hpos hmono hN (fun k _ => by positivity), Complex.ofReal_sum,
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by rw [Complex.ofReal_mul, div_pow, mul_assoc],
      integral_finsetSum]
    · exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul, fourierInv_inv_one_add_sq (hpos k) s]
    · intro k _
      have hint := integrable_inv_one_add_div_sq (hpos k)
      exact (hint.norm.const_mul ‖(pfCoeff lam N k : ℂ)‖).mono'
        ((hint.aestronglyMeasurable.mul (by fun_prop)).const_mul _)
        (Eventually.of_forall fun ξ => by rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one])
  have hEN_bound : ∀ N ≥ q + 1, ‖iteratedDeriv q (EN N) t‖ ≤ Dbound ε q := fun N hN => by
    rw [hEN_eq N (by lia), iteratedDeriv_fun_sum fun k _ => by
      have hcd : ∀ c : ℂ, ContDiff ℝ ∞ (fun s : ℝ => (pfCoeff lam N k : ℂ) *
          (((lam k / 2 : ℝ) : ℂ) * Complex.exp (c * (s : ℂ)))) := fun c =>
        contDiff_const.mul (contDiff_const.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp))
      rcases lt_or_gt_of_ne ht0 with h | h
      · exact ((hcd (lam k : ℂ)).contDiffAt.of_le (by simp)).congr_of_eventuallyEq <| by
          filter_upwards [Iio_mem_nhds h] with s hs; simp [abs_of_neg (hs : s < 0), Complex.ofReal_exp]
      · exact ((hcd (-(lam k : ℂ))).contDiffAt.of_le (by simp)).congr_of_eventuallyEq <| by
          filter_upwards [Ioi_mem_nhds h] with s hs; simp [abs_of_pos (hs : 0 < s), Complex.ofReal_exp]]
    have hgeo3 := geom_sum_le_inv_one_sub (r := 1 / 3) (by norm_num) (by norm_num) N
    norm_num at hgeo3
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range N, ‖iteratedDeriv q
            (fun s : ℝ => (pfCoeff lam N k : ℂ) * ((lam k / 2 * Real.exp (-lam k * |s|) : ℝ) : ℂ)) t‖
        ≤ ∑ k ∈ Finset.range N, (1 / 3 : ℝ) ^ k * ((q + 1).factorial * (2 / ε) ^ (q + 1)) :=
          Finset.sum_le_sum fun k hk => by
            rw [iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              iteratedDeriv_exp_neg_abs_norm (hpos k) ht0 q]
            have hlk := hpos k
            have h1 := Real.pow_div_factorial_le_exp (lam k * (ε / 2)) (by positivity) (q + 1)
            have hexp : lam k ^ (q + 1) * Real.exp (-lam k * |t|) ≤
                (q + 1).factorial * (2 / ε) ^ (q + 1) := by
              calc lam k ^ (q + 1) * Real.exp (-lam k * |t|)
                  ≤ lam k ^ (q + 1) * (Real.exp (lam k * (ε / 2)))⁻¹ :=
                    mul_le_mul_of_nonneg_left (by rw [← Real.exp_neg]; exact Real.exp_le_exp.2 (by nlinarith))
                      (by positivity)
                _ ≤ lam k ^ (q + 1) * ((lam k * (ε / 2)) ^ (q + 1) / (q + 1).factorial)⁻¹ :=
                    mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h1) (by positivity)
                _ = (q + 1).factorial * (2 / ε) ^ (q + 1) := by
                    rw [mul_pow, div_pow, div_pow, inv_div]; field_simp [hlk.ne', hε.ne']
            calc |pfCoeff lam N k| * (lam k ^ (q + 1) * Real.exp (-lam k * |t|) / 2)
                ≤ (2 * (1 / 3 : ℝ) ^ k) * (lam k ^ (q + 1) * Real.exp (-lam k * |t|) / 2) :=
                  mul_le_mul_of_nonneg_right (abs_pfCoeff_le hpos hstep (Finset.mem_range.1 hk)) (by positivity)
              _ = (1 / 3 : ℝ) ^ k * (lam k ^ (q + 1) * Real.exp (-lam k * |t|)) := by ring
              _ ≤ (1 / 3 : ℝ) ^ k * ((q + 1).factorial * (2 / ε) ^ (q + 1)) :=
                  mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (∑ k ∈ Finset.range N, (1 / 3 : ℝ) ^ k) * ((q + 1).factorial * (2 / ε) ^ (q + 1)) :=
          (Finset.sum_mul ..).symm
      _ ≤ Dbound ε q := by
          dsimp [Dbound]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hgeo3 (by positivity)
  have htend : Tendsto (fun N => iteratedDeriv q (EN N) t) atTop
      (𝓝 (iteratedDeriv q (fundSol lam) t)) := by
    rw [iteratedDeriv_fundSol hlam hmono.monotone q t]
    refine Tendsto.congr' (by
      filter_upwards [eventually_ge_atTop (q + 1)] with N hN
      exact (congrFun (iteratedDeriv_fourierInv_eq
        (fun k hk => integrable_pow_div_prodPoly hpos hmono.monotone (by lia)) q le_rfl) t).symm)
      (tendsto_integral_filter_of_dominated_convergence
        (fun ξ => ‖(2 * π * I * ξ) ^ q * (((prodPoly lam (q + 1) ((2 * π * ξ) ^ 2))⁻¹ : ℝ) : ℂ)‖)
        (Eventually.of_forall fun N =>
          (((by fun_prop : Continuous fun ξ : ℝ => (2 * π * I * ξ) ^ q).mul
            (Complex.continuous_ofReal.comp ((continuous_prodPoly lam N).inv₀ fun ξ =>
              (lt_of_lt_of_le zero_lt_one (one_le_prodPoly lam N (sq_nonneg _))).ne'))).mul
            (by fun_prop)).aestronglyMeasurable)
        (by
          filter_upwards [eventually_ge_atTop (q + 1)] with N hN
          refine Eventually.of_forall fun ξ => ?_
          simp only [Pi.mul_apply, Function.comp_apply, Pi.inv_apply]
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul, norm_mul,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          have h1 : 0 < prodPoly lam (q + 1) ((2 * π * ξ) ^ 2) :=
            lt_of_lt_of_le zero_lt_one (one_le_prodPoly lam (q + 1) (sq_nonneg _))
          have h2 := prodPoly_mono lam (sq_nonneg (2 * π * ξ)) hN
          rw [abs_of_pos (inv_pos.2 (h1.trans_le h2)), abs_of_pos (inv_pos.2 h1)]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ h1 h2) (norm_nonneg _))
        (integrable_pow_div_prodPoly hpos hmono.monotone (le_refl (q + 1))).norm
        (Eventually.of_forall fun ξ => by
          have ht1 := (tendsto_prodPoly hlam (sq_nonneg (2 * π * ξ))).inv₀
            (lt_of_lt_of_le zero_lt_one (one_le_infProd hlam (sq_nonneg _))).ne'
          simpa [Function.comp_def] using
            (((Complex.continuous_ofReal.tendsto _).comp ht1).const_mul ((2 * π * I * ξ) ^ q)).mul_const
              (Complex.exp (↑(2 * π * t * ξ) * I))))
  exact le_of_tendsto htend.norm (eventually_atTop.2 ⟨q + 1, hEN_bound⟩)

/-! ### Integration by parts and distributional identity for `fundSol` -/

private lemma contDiff_iteratedDeriv_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (m : ℕ) : ContDiff ℝ ∞ (iteratedDeriv m f) := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv m

private lemma hasCompactSupport_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : HasCompactSupport f) : ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f)
  | 0 => by simpa using hf
  | n + 1 => by rw [iteratedDeriv_succ]; exact (hasCompactSupport_iteratedDeriv hf n).deriv

private lemma integral_mul_iteratedDeriv {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∀ n : ℕ, ∫ t, F t * iteratedDeriv n ψ t = (-1 : ℂ) ^ n * ∫ t, iteratedDeriv n F t * ψ t := by
  intro n; induction n generalizing F with
  | zero => simp
  | succ n ih =>
    have hψn := contDiff_iteratedDeriv_infty hψ n
    have hψnc := hasCompactSupport_iteratedDeriv hψc n
    have hibp : ∫ t, F t * deriv (iteratedDeriv n ψ) t = -∫ t, deriv F t * iteratedDeriv n ψ t :=
      integral_mul_deriv_eq_deriv_mul_of_integrable
        (fun x _ => (hF.differentiable (by simp) x).hasDerivAt)
        (fun x _ => (hψn.differentiable (by simp) x).hasDerivAt)
        ((hF.continuous.mul (hψn.continuous_deriv (by simp))).integrable_of_hasCompactSupport
          hψnc.deriv.mul_left)
        (((hF.continuous_deriv (by simp)).mul hψn.continuous).integrable_of_hasCompactSupport
          hψnc.mul_left)
        ((hF.continuous.mul hψn.continuous).integrable_of_hasCompactSupport hψnc.mul_left)
    rw [iteratedDeriv_succ, hibp,
      ih (by simpa [iteratedDeriv_one] using contDiff_iteratedDeriv_infty hF 1)]
    simp_rw [← iteratedDeriv_succ']; rw [pow_succ]; ring

private lemma tsum_iteratedDeriv_fundSol {lam : ℕ → ℝ} (hlam : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k)
    (hmono : Monotone lam) {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) :
    ∑' m : ℕ, ((-1 : ℂ) ^ m * (bLim lam m : ℂ)) *
        ∫ t, Φ t * iteratedDeriv (2 * m) (fundSol lam) t = Φ 0 := by
  let Φs : SchwartzMap ℝ ℂ := hΦc.toSchwartzMap hΦ
  have hΦ_int : Integrable Φ := Φs.integrable
  have hFΦ_int : Integrable (𝓕 Φ) := by
    change Integrable (𝓕 (Φs : ℝ → ℂ)); rw [← SchwartzMap.fourier_coe]; exact (𝓕 Φs).integrable
  have hFΦinv_int : Integrable (𝓕⁻ Φ) := by
    change Integrable (𝓕⁻ (Φs : ℝ → ℂ)); rw [← SchwartzMap.fourierInv_coe]; exact (𝓕⁻ Φs).integrable
  set P : ℝ → ℝ := fun ξ => infProd lam ((2 * π * ξ) ^ 2)
  have hmeasP : Measurable P := measurable_infProd hlam
  have hPpos : ∀ ξ : ℝ, 0 < P ξ := fun ξ => lt_of_lt_of_le zero_lt_one (one_le_infProd hlam (sq_nonneg _))
  let w : ℕ → ℝ → ℝ := fun m ξ => bLim lam m * ((2 * π * ξ) ^ 2) ^ m / P ξ
  have hw_nn : ∀ m ξ, 0 ≤ w m ξ := fun m ξ =>
    div_nonneg (mul_nonneg (bLim_nonneg hlam m) (by positivity)) (hPpos ξ).le
  have hw_le : ∀ m ξ, w m ξ ≤ 1 := fun m ξ =>
    (div_le_one (hPpos ξ)).2 <| (summable_infProd hlam (sq_nonneg _)).le_tsum m
      fun j _ => mul_nonneg (bLim_nonneg hlam j) (by positivity)
  have hterm : ∀ m : ℕ,
      ((-1 : ℂ) ^ m * (bLim lam m : ℂ)) * ∫ t, Φ t * iteratedDeriv (2 * m) (fundSol lam) t =
        ∫ ξ : ℝ, (w m ξ : ℂ) * 𝓕⁻ Φ ξ := fun m => by
    have hprod_int : Integrable (Function.uncurry fun t ξ : ℝ =>
        Φ t * ((2 * π * I * ξ) ^ (2 * m) * (((P ξ)⁻¹ : ℝ) : ℂ) *
          Complex.exp (↑(2 * π * t * ξ) * I))) (volume.prod volume) :=
      (hΦ_int.norm.mul_prod (integrable_pow_div_infProd hlam hmono (2 * m)).norm).mono'
        ((hΦ.continuous.measurable.comp measurable_fst).mul
          ((((by fun_prop : Continuous fun ξ : ℝ => (2 * π * I * ξ) ^ (2 * m)).measurable.comp
            measurable_snd).mul
            ((Complex.continuous_ofReal.measurable.comp hmeasP.inv).comp measurable_snd)).mul
            (by fun_prop : Continuous fun p : ℝ × ℝ =>
              Complex.exp (↑(2 * π * p.1 * p.2) * I)).measurable)).aestronglyMeasurable
        (Eventually.of_forall fun ⟨_, _⟩ => by
          simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; rfl)
    have hswap : ∫ t, Φ t * iteratedDeriv (2 * m) (fundSol lam) t =
        ∫ ξ : ℝ, (2 * π * I * ξ) ^ (2 * m) * (((P ξ)⁻¹ : ℝ) : ℂ) * 𝓕⁻ Φ ξ := by
      simp_rw [iteratedDeriv_fundSol hlam hmono (2 * m), ← integral_const_mul]
      rw [integral_integral_swap hprod_int]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      dsimp only; rw [Real.fourierInv_eq', ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by
        simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
        rw [mul_comm ξ t, ← mul_assoc (2 * π)]; ring)
    rw [hswap, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only [w]
    have hpow : (2 * π * I * ξ : ℂ) ^ (2 * m) =
        (-1 : ℂ) ^ m * ((((2 * π * ξ) ^ 2) ^ m : ℝ) : ℂ) := by
      rw [show (2 * π * I * ξ : ℂ) = I * ((2 * π * ξ : ℝ) : ℂ) by push_cast; ring,
        mul_pow, pow_mul, Complex.I_sq, pow_mul, Complex.ofReal_pow, Complex.ofReal_pow]
    have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by rw [← mul_pow]; simp
    rw [hpow, Complex.ofReal_div, Complex.ofReal_mul, div_eq_mul_inv, Complex.ofReal_inv]
    calc (-1 : ℂ) ^ m * (bLim lam m : ℂ) *
            ((-1 : ℂ) ^ m * ((((2 * π * ξ) ^ 2) ^ m : ℝ) : ℂ) * (P ξ : ℂ)⁻¹ * 𝓕⁻ Φ ξ)
        = ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) * ((bLim lam m : ℂ) *
            ((((2 * π * ξ) ^ 2) ^ m : ℝ) : ℂ) * (P ξ : ℂ)⁻¹ * 𝓕⁻ Φ ξ) := by ring
      _ = (bLim lam m : ℂ) * ((((2 * π * ξ) ^ 2) ^ m : ℝ) : ℂ) * (P ξ : ℂ)⁻¹ * 𝓕⁻ Φ ξ := by
          rw [hsign, one_mul]
  have hint_w : ∀ m, Integrable (fun ξ : ℝ => (w m ξ : ℂ) * 𝓕⁻ Φ ξ) := fun m =>
    hFΦinv_int.norm.mono'
      ((Complex.continuous_ofReal.measurable.comp
        ((continuous_const.mul (by fun_prop)).measurable.div hmeasP)).aestronglyMeasurable.mul
        hFΦinv_int.aestronglyMeasurable)
      (Eventually.of_forall fun ξ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nn m ξ)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hw_le m ξ))
  have hsum_w : Summable (fun m => ∫ ξ : ℝ, ‖(w m ξ : ℂ) * 𝓕⁻ Φ ξ‖) := by
    refine summable_of_sum_range_le (c := ∫ ξ : ℝ, ‖𝓕⁻ Φ ξ‖)
      (fun _ => integral_nonneg fun _ => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ fun m _ => (hint_w m).norm]
    refine integral_mono (integrable_finsetSum _ fun m _ => (hint_w m).norm) hFΦinv_int.norm fun ξ => ?_
    have hle : ∑ m ∈ Finset.range N, w m ξ ≤ 1 := by
      rw [show ∑ m ∈ Finset.range N, w m ξ =
        (∑ m ∈ Finset.range N, bLim lam m * ((2 * π * ξ) ^ 2) ^ m) / P ξ from (Finset.sum_div ..).symm]
      exact (div_le_one (hPpos ξ)).2 <| (summable_infProd hlam (sq_nonneg _)).sum_le_tsum _
        fun j _ => mul_nonneg (bLim_nonneg hlam j) (by positivity)
    calc ∑ m ∈ Finset.range N, ‖(w m ξ : ℂ) * 𝓕⁻ Φ ξ‖
        = (∑ m ∈ Finset.range N, w m ξ) * ‖𝓕⁻ Φ ξ‖ := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nn m ξ)]
      _ ≤ ‖𝓕⁻ Φ ξ‖ := mul_le_of_le_one_left (norm_nonneg _) hle
  simp_rw [hterm]
  rw [integral_tsum_of_summable_integral_norm hint_w hsum_w]
  simp_rw [show ∀ ξ : ℝ, ∑' m : ℕ, (w m ξ : ℂ) * 𝓕⁻ Φ ξ = 𝓕⁻ Φ ξ from fun ξ => by
    rw [tsum_mul_right, ← Complex.ofReal_tsum,
      show ∑' m : ℕ, w m ξ = 1 by simp only [w, tsum_div_const]; exact div_self (hPpos ξ).ne',
      Complex.ofReal_one, one_mul]]
  have hinv := congrFun (hΦ.continuous.fourier_fourierInv_eq hΦ_int hFΦ_int) 0
  rw [Real.fourier_eq'] at hinv
  simpa using hinv

/-! ### Main 1D Dixmier-Malliavin factorization theorem -/

private lemma norm_iteratedDeriv_commutator_le {χ E : ℝ → ℂ} {C : ℕ → ℝ} {ε : ℝ}
    (hχ_cd : ContDiff ℝ ∞ χ) (hE_cd : ContDiff ℝ ∞ E)
    (hχ_dz : ∀ {t : ℝ}, |t| < ε / 2 → ∀ {j : ℕ}, 1 ≤ j → iteratedDeriv j χ t = 0)
    (hC_nn : ∀ j, 0 ≤ C j) (hC_bd : ∀ j t, ‖iteratedDeriv j χ t‖ ≤ C j)
    (hE_bd : ∀ q {t : ℝ}, ε / 2 ≤ |t| → ‖iteratedDeriv q E t‖ ≤ Dbound ε q)
    (hε : 0 < ε) (m r : ℕ) (t : ℝ) :
    ‖iteratedDeriv r (fun s => iteratedDeriv (2 * m) (χ * E) s - χ s * iteratedDeriv (2 * m) E s) t‖ ≤
      ∑ j ∈ Finset.Icc 1 (2 * m), ((2 * m).choose j : ℝ) *
        ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * C (j + i) * Dbound ε (2 * m - j + r - i) := by
  have hcdAt : ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ (n : ℕ) (s : ℝ), ContDiffAt ℝ n f s :=
    fun hf _ _ => hf.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have heq : (fun s => iteratedDeriv (2 * m) (χ * E) s - χ s * iteratedDeriv (2 * m) E s) =
      fun s => ∑ j ∈ Finset.Icc 1 (2 * m), (((2 * m).choose j : ℕ) : ℂ) *
        iteratedDeriv j χ s * iteratedDeriv (2 * m - j) E s := funext fun s => by
    rw [iteratedDeriv_mul (hcdAt hχ_cd _ s) (hcdAt hE_cd _ s), ← Nat.Ico_zero_eq_range,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
    simp [Finset.Ico_add_one_right_eq_Icc]
  rw [heq, iteratedDeriv_fun_sum fun j _ =>
    (contDiffAt_const.mul (hcdAt (contDiff_iteratedDeriv_infty hχ_cd j) r t)).mul
      (hcdAt (contDiff_iteratedDeriv_infty hE_cd _) r t)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have hj2 : j ≤ 2 * m := (Finset.mem_Icc.1 hj).2
  simp_rw [mul_assoc ((((2 * m).choose j : ℕ) : ℂ))]
  rw [iteratedDeriv_const_mul_field, norm_mul, Complex.norm_natCast,
    show (fun x => iteratedDeriv j χ x * iteratedDeriv (2 * m - j) E x) =
      iteratedDeriv j χ * iteratedDeriv (2 * m - j) E from rfl,
    iteratedDeriv_mul (hcdAt (contDiff_iteratedDeriv_infty hχ_cd j) r t)
      (hcdAt (contDiff_iteratedDeriv_infty hE_cd _) r t)]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_))
    (Nat.cast_nonneg _)
  have hi_le : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hiter : ∀ {f : ℝ → ℂ} (a b : ℕ), iteratedDeriv a (iteratedDeriv b f) = iteratedDeriv (a + b) f :=
    fun a b => by simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]
  rw [hiter, hiter, norm_mul, norm_mul, Complex.norm_natCast]
  by_cases ht : |t| < ε / 2
  · rw [show i + j = j + i by lia, hχ_dz ht (by lia), norm_zero, mul_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC_nn _)) (by dsimp [Dbound]; positivity)
  · push Not at ht
    rw [show i + j = j + i by lia, show r - i + (2 * m - j) = 2 * m - j + r - i by lia]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hC_bd (j + i) t) (Nat.cast_nonneg _))
      (hE_bd _ ht) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC_nn _))

public theorem exists_dixmierMalliavin_line (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → ℝ) (g h : ℝ → ℂ), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      tsupport g ⊆ Set.Icc (-ε) ε ∧ tsupport h ⊆ Set.Icc (-ε) ε ∧
      Summable (fun p => |c p| * M p) ∧
      ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → (∀ p, ∀ t ∈ Set.Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p) →
        F 0 = (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) + ∫ t, F t * h t := by
  let bump : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by linarith, by linarith⟩
  let χ : ℝ → ℂ := fun t => (bump t : ℂ)
  have hχ_cd : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hχ_supp : tsupport χ ⊆ Set.Icc (-ε) ε :=
    (closure_mono fun t ht => by simpa [χ] using ht : tsupport χ ⊆ tsupport (bump : ℝ → ℝ)).trans <| by
      change tsupport (bump : ℝ → ℝ) ⊆ _
      rw [bump.tsupport_eq]; intro t ht; simpa [Metric.mem_closedBall, dist_zero_right, abs_le] using ht
  have hχ_comp : HasCompactSupport χ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) hχ_supp
  have hχ_zero : χ 0 = 1 := by
    simp [χ, bump.one_of_mem_closedBall (Metric.mem_closedBall_self (by linarith : (0 : ℝ) ≤ ε / 2))]
  have hχ_deriv_zero : ∀ {t : ℝ}, |t| < ε / 2 → ∀ {j : ℕ}, 1 ≤ j → iteratedDeriv j χ t = 0 := by
    intro t ht j hj
    have hev : χ =ᶠ[𝓝 t] fun _ => (1 : ℂ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (by simpa [Metric.mem_ball, dist_zero_right] using ht : t ∈ Metric.ball (0 : ℝ) (ε / 2))]
        with s hs
      simp [χ, bump.one_of_mem_closedBall (Metric.ball_subset_closedBall hs)]
    rw [hev.iteratedDeriv_eq]; cases j with | zero => lia | succ j => rw [iteratedDeriv_succ']; simp
  choose C hC_nonneg hC_bound using fun j : ℕ => show ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv j χ t‖ ≤ C by
    obtain ⟨C, hC⟩ := (hasCompactSupport_iteratedDeriv hχ_comp j).exists_bound_of_continuous
      (contDiff_iteratedDeriv_infty hχ_cd j).continuous
    exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩
  let W : ℕ → ℕ → ℝ := fun m r =>
    ∑ j ∈ Finset.Icc 1 (2 * m), ((2 * m).choose j : ℝ) *
      ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * C (j + i) * Dbound ε (2 * m - j + r - i)
  have hW_nn : ∀ m r, 0 ≤ W m r := fun m r =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) <|
      Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC_nonneg _))
        (by dsimp [Dbound]; positivity)
  let Wstar : ℕ → ℝ := fun m => ∑ r ∈ Finset.range (m + 1), W m r
  have hWstar_nn : ∀ m, 0 ≤ Wstar m := fun m => Finset.sum_nonneg fun r _ => hW_nn m r
  let δ : ℕ → ℝ := fun m => 1 / (2 ^ m * (1 + |M (2 * m)| + Wstar m))
  have hδ_pos : ∀ m, 0 < δ m := fun m => by
    have : 0 < 1 + |M (2 * m)| + Wstar m := by linarith [abs_nonneg (M (2 * m)), hWstar_nn m]
    dsimp [δ]; positivity
  obtain ⟨lam, hlam0, hlam_step, hb_le_δ⟩ := exists_lam δ hδ_pos
  have hlam_pow : ∀ k, (2 : ℝ) ^ (k + 1) ≤ lam k := fun k => by
    induction k with | zero => simpa using hlam0 | succ k ih => rw [pow_succ']; linarith [hlam_step k]
  have hlam_mono : Monotone lam := monotone_nat_of_le_succ fun k => by
    linarith [hlam_step k, lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 ^ (k + 1)) (hlam_pow k)]
  let b : ℕ → ℝ := bLim lam
  have hb0 : b 0 = 1 := bLim_zero lam
  have hb_nn : ∀ m, 0 ≤ b m := bLim_nonneg hlam_pow
  have hδ_mul : ∀ m x, x ≤ 1 + |M (2 * m)| + Wstar m → δ m * x ≤ (1 / 2 : ℝ) ^ m := fun m x hx => by
    have hden : 0 < 1 + |M (2 * m)| + Wstar m := by linarith [abs_nonneg (M (2 * m)), hWstar_nn m]
    dsimp [δ]; rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    exact hx.trans_eq (by rw [one_div, inv_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul])
  have hbM_le : ∀ m, b m * |M (2 * m)| ≤ max 1 |M 0| * (1 / 2 : ℝ) ^ m := fun m => by
    cases m with
    | zero => simp [hb0]
    | succ m =>
      have h1 : b (m + 1) * |M (2 * (m + 1))| ≤ (1 / 2 : ℝ) ^ (m + 1) :=
        (mul_le_mul_of_nonneg_right (hb_le_δ (m + 1) (by lia)) (abs_nonneg _)).trans
          (hδ_mul (m + 1) _ (by linarith [hWstar_nn (m + 1)]))
      exact h1.trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
  have hbW_le : ∀ m r, r ≤ m → b m * W m r ≤ (1 / 2 : ℝ) ^ m := fun m r hr => by
    cases m with
    | zero => simp [W]
    | succ m =>
      exact (mul_le_mul (hb_le_δ (m + 1) (by lia)) (Finset.single_le_sum (s := Finset.range (m + 2))
        (fun i _ => hW_nn (m + 1) i) (Finset.mem_range.2 (by lia))) (hW_nn _ _) (hδ_pos _).le).trans
        (hδ_mul (m + 1) _ (by linarith [abs_nonneg (M (2 * (m + 1)))]))
  let E : ℝ → ℂ := fundSol lam
  have hE_cd : ContDiff ℝ ∞ E := contDiff_fundSol hlam_pow hlam_mono
  let g : ℝ → ℂ := χ * E
  have hg_cd : ContDiff ℝ ∞ g := hχ_cd.mul hE_cd
  have hg_supp : tsupport g ⊆ Set.Icc (-ε) ε :=
    (closure_mono (Function.support_mul_subset_left χ E)).trans hχ_supp
  have hg_comp : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hg_supp
  let hTerm : ℕ → ℝ → ℂ := fun m t =>
    -((-1 : ℂ) ^ m * (b m : ℂ)) * (iteratedDeriv (2 * m) (χ * E) t - χ t * iteratedDeriv (2 * m) E t)
  have hhTerm_cd : ∀ m, ContDiff ℝ ∞ (hTerm m) := fun m =>
    contDiff_const.mul ((contDiff_iteratedDeriv_infty hg_cd _).sub
      (hχ_cd.mul (contDiff_iteratedDeriv_infty hE_cd _)))
  have hhTerm_deriv_bound : ∀ r m t, ‖iteratedDeriv r (hTerm m) t‖ ≤ b m * W m r := fun r m t => by
    dsimp only [hTerm]
    rw [iteratedDeriv_const_mul_field, norm_mul, norm_neg, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb_nn m)]
    exact mul_le_mul_of_nonneg_left
      (norm_iteratedDeriv_commutator_le hχ_cd hE_cd hχ_deriv_zero hC_nonneg hC_bound
        (fun q {_} ht => norm_iteratedDeriv_fundSol_le hlam0 hlam_step hε q ht) hε m r t) (hb_nn m)
  let h : ℝ → ℂ := fun t => ∑' m : ℕ, hTerm m t
  have hh_cd : ContDiff ℝ ∞ h :=
    contDiff_tsum_of_eventually (v := fun _ m => (1 / 2 : ℝ) ^ m) hhTerm_cd
      (fun _ _ => summable_geometric_two) fun r _ => by
        rw [Filter.eventually_cofinite]
        refine (Set.finite_Iio r).subset fun m hm => ?_
        simp only [Set.mem_ofPred_eq, not_forall, not_le] at hm
        rcases hm with ⟨t, ht⟩
        by_contra hmr; simp only [Set.mem_Iio, not_lt] at hmr
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at ht
        linarith [(hhTerm_deriv_bound r m t).trans (hbW_le m r hmr)]
  have hhTerm_supp : ∀ m, support (hTerm m) ⊆ Set.Icc (-ε) ε := fun m t ht => by
    by_contra hnot
    have hev_χ : χ =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hnot (hχ_supp h)
    have hev_g : (χ * E) =ᶠ[𝓝 t] 0 := by filter_upwards [hev_χ] with s hs; simp [hs]
    exact ht (by simp [hTerm, hev_χ.eq_of_nhds, hev_g.iteratedDeriv_eq])
  have hh_supp : tsupport h ⊆ Set.Icc (-ε) ε :=
    closure_minimal (fun t ht => by_contra fun hnot => ht <| by
      have h0 : ∀ m, hTerm m t = 0 := fun m => by_contra fun hm => hnot (hhTerm_supp m hm)
      simp [h, h0]) isClosed_Icc
  let c : ℕ → ℝ := fun p => if Even p then (-1 : ℝ) ^ (p / 2) * b (p / 2) else 0
  have hc_summable : Summable (fun p => |c p| * M p) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (r := 3 / 4) (by norm_num) (by norm_num)).mul_left (max 1 |M 0|))
      fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_abs]
    by_cases hev : Even p
    · rcases hev with ⟨m, rfl⟩
      have hcm : |c (m + m)| = b m := by
        simp [c, show Even (m + m) from ⟨m, rfl⟩, show (m + m) / 2 = m by lia, abs_of_nonneg (hb_nn m)]
      rw [hcm, show m + m = 2 * m by lia]
      calc b m * |M (2 * m)| ≤ max 1 |M 0| * (1 / 2 : ℝ) ^ m := hbM_le m
        _ ≤ max 1 |M 0| * (9 / 16 : ℝ) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by positivity)
        _ = max 1 |M 0| * (3 / 4 : ℝ) ^ (2 * m) := by rw [pow_mul]; norm_num
    · simp [c, hev]; positivity
  refine ⟨c, g, h, hg_cd, hh_cd, hg_supp, hh_supp, hc_summable, fun F hF hFM => ?_⟩
  have hSeries1_eq : (∑' p : ℕ, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) =
      ∑' m : ℕ, ((-1 : ℂ) ^ m * (b m : ℂ)) * ∫ t, iteratedDeriv (2 * m) F t * g t :=
    tsum_eq_tsum_of_ne_zero_bij (fun m => 2 * m.1) (fun _ _ hab => Subtype.ext (by lia))
      (fun p hp => by
        simp only [Function.mem_support, ne_eq] at hp
        rcases (by_contra fun hne => hp (by simp [c, hne]) : Even p) with ⟨m, rfl⟩
        exact ⟨⟨m, fun hm => hp <| by
          simpa [c, show Even (m + m) from ⟨m, rfl⟩, show m + m = 2 * m by lia,
            Nat.mul_div_cancel_left _ two_pos] using hm⟩, by lia⟩)
      fun m => by simp [c, Nat.mul_div_cancel_left _ two_pos]
  have hS1_summable : Summable (fun m : ℕ =>
      ((-1 : ℂ) ^ m * (b m : ℂ)) * ∫ t, iteratedDeriv (2 * m) F t * g t) := by
    have hg_int_norm : Integrable (fun t => ‖g t‖) :=
      (hg_cd.continuous.integrable_of_hasCompactSupport hg_comp).norm
    refine Summable.of_norm_bounded
      ((summable_geometric_two.mul_left (max 1 |M 0|)).mul_right (∫ t, ‖g t‖)) fun m => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb_nn m)]
    have hint_le : ‖∫ t, iteratedDeriv (2 * m) F t * g t‖ ≤ |M (2 * m)| * ∫ t, ‖g t‖ := by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono (((contDiff_iteratedDeriv_infty hF (2 * m)).continuous.mul
        hg_cd.continuous).integrable_of_hasCompactSupport hg_comp.mul_left).norm
        (hg_int_norm.const_mul _) fun t => ?_
      rw [norm_mul]
      by_cases hgt : g t = 0
      · simp [hgt]
      · exact mul_le_mul_of_nonneg_right
          ((hFM (2 * m) t (hg_supp (subset_closure hgt))).trans (le_abs_self _)) (norm_nonneg _)
    calc b m * ‖∫ t, iteratedDeriv (2 * m) F t * g t‖
        ≤ (b m * |M (2 * m)|) * ∫ t, ‖g t‖ := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hint_le (hb_nn m)
      _ ≤ max 1 |M 0| * (1 / 2 : ℝ) ^ m * ∫ t, ‖g t‖ :=
          mul_le_mul_of_nonneg_right (hbM_le m) (integral_nonneg fun _ => norm_nonneg _)
  have hhTerm_comp : ∀ m, HasCompactSupport (hTerm m) := fun m =>
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal (hhTerm_supp m) isClosed_Icc)
  have hFi : ∀ m : ℕ, Integrable (fun t => F t * hTerm m t) := fun m =>
    (hF.continuous.mul (hhTerm_cd m).continuous).integrable_of_hasCompactSupport (hhTerm_comp m).mul_left
  have hsum_int : Summable (fun m : ℕ => ∫ t, ‖F t * hTerm m t‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => by
      calc ∫ t, ‖F t * hTerm m t‖
          ≤ ∫ t, Set.indicator (Set.Icc (-ε) ε) (fun _ => |M 0| * (1 / 2 : ℝ) ^ m) t :=
            integral_mono (hFi m).norm
              ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc) fun t => by
                by_cases ht : t ∈ Set.Icc (-ε) ε
                · rw [Set.indicator_of_mem ht, norm_mul]
                  exact mul_le_mul ((by simpa using hFM 0 t ht : ‖F t‖ ≤ M 0).trans (le_abs_self _))
                    ((by simpa using hhTerm_deriv_bound 0 m t : ‖hTerm m t‖ ≤ b m * W m 0).trans
                      (hbW_le m 0 (Nat.zero_le m))) (norm_nonneg _) (abs_nonneg _)
                · rw [Set.indicator_of_notMem ht]
                  have h0 : hTerm m t = 0 := by_contra fun hne => ht (hhTerm_supp m hne)
                  simp [h0]
        _ = (|M 0| * (2 * ε)) * (1 / 2 : ℝ) ^ m := by
            rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
              Real.volume_real_Icc_of_le (by linarith : -ε ≤ ε)]; ring)
      (summable_geometric_two.mul_left _)
  have hSeries2_eq : ∫ t, F t * h t = ∑' m : ℕ, ∫ t, F t * hTerm m t := by
    rw [show (fun t => F t * h t) = fun t => ∑' m : ℕ, F t * hTerm m t from
      funext fun t => by dsimp [h]; rw [tsum_mul_left],
      ← integral_tsum_of_summable_integral_norm hFi hsum_int]
  have hS2_summable : Summable (fun m : ℕ => ∫ t, F t * hTerm m t) :=
    Summable.of_norm_bounded hsum_int fun m => norm_integral_le_integral_norm _
  have hcancel : ∀ m : ℕ,
      ((-1 : ℂ) ^ m * (b m : ℂ)) * (∫ t, iteratedDeriv (2 * m) F t * g t) +
        (∫ t, F t * hTerm m t) =
      ((-1 : ℂ) ^ m * (b m : ℂ)) * ∫ t, (F * χ) t * iteratedDeriv (2 * m) E t := fun m => by
    have hibp : ∫ t, F t * iteratedDeriv (2 * m) (χ * E) t = ∫ t, iteratedDeriv (2 * m) F t * g t := by
      simpa [g, pow_mul] using integral_mul_iteratedDeriv hF hg_cd hg_comp (2 * m)
    have hh_int : ∫ t, F t * hTerm m t =
        -((-1 : ℂ) ^ m * (b m : ℂ)) *
          ((∫ t, F t * iteratedDeriv (2 * m) (χ * E) t) -
            ∫ t, F t * (χ t * iteratedDeriv (2 * m) E t)) := by
      have hi1 : Integrable (fun t => F t * iteratedDeriv (2 * m) (χ * E) t) :=
        (hF.continuous.mul (contDiff_iteratedDeriv_infty hg_cd _).continuous).integrable_of_hasCompactSupport
          (hasCompactSupport_iteratedDeriv hg_comp _).mul_left
      have hi2 : Integrable (fun t => F t * (χ t * iteratedDeriv (2 * m) E t)) :=
        (hF.continuous.mul (hχ_cd.continuous.mul
          (contDiff_iteratedDeriv_infty hE_cd _).continuous)).integrable_of_hasCompactSupport
          hχ_comp.mul_right.mul_left
      rw [← integral_sub hi1 hi2, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by dsimp only [hTerm]; ring)
    rw [hh_int, hibp, show ∫ t, F t * (χ t * iteratedDeriv (2 * m) E t) =
      ∫ t, (F * χ) t * iteratedDeriv (2 * m) E t from
        integral_congr_ae (Eventually.of_forall fun t => by simp [mul_assoc])]
    ring
  rw [hSeries1_eq, hSeries2_eq, ← hS1_summable.tsum_add hS2_summable]
  simp_rw [hcancel]
  have hmain := tsum_iteratedDeriv_fundSol hlam_pow hlam_mono (hF.mul hχ_cd) hχ_comp.mul_left
  simp only [hχ_zero, mul_one] at hmain
  exact hmain.symm

end
end GroundTheory.Automorphic
