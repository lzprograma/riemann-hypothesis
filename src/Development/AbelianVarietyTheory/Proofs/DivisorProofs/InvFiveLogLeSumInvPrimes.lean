module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial

@[expose] public section

open Classical

namespace GlobalTheory.PrimeRecip

/-- Candidate primes that work for every `N` in `[a, b)`. A composite at most
`a` has a factor between 2 and `√a`, so it cannot pass the gcd test. -/
private def witnesses (a b : ℕ) : Finset ℕ :=
  (Finset.Icc ((b + 1) / 2) (a - 3)).filter fun p => p.Coprime a.sqrt.factorial

private theorem interval_bound {a b N : ℕ} (ha : 100 ≤ a) (haN : a ≤ N) (hNb : N < b)
    (hc : 3 * a ≤ 10 * (witnesses a b).card * a.log2) :
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  have hsub : witnesses a b ⊆
      (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro p hp
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hrange
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, by omega, by omega⟩
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega, fun d hd hdp hdvd => ?_⟩
    have hda := hdp.trans (Nat.sqrt_le_sqrt (show p ≤ a by omega))
    have := Nat.eq_one_of_dvd_coprimes hcop hdvd (Nat.dvd_factorial (by omega) hda)
    omega
  -- Each witness contributes at least 1/a, and log N ≥ log₂(a) · log 2.
  have hpow : 2 ^ a.log2 ≤ N := (Nat.log2_self_le (by omega)).trans haN
  have hlog := Real.log_le_log (by positivity) (show (2 : ℝ) ^ a.log2 ≤ N by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have htwo : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog' := (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg a.log2)).trans hlog
  have hc' : 3 * (a : ℝ) ≤ 10 * (witnesses a b).card * a.log2 := by exact_mod_cast hc
  have ha' : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hN' : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    1 / (5 * Real.log N) ≤ (witnesses a b).card * (1 / (a : ℝ)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) ha']
      linarith [mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg (witnesses a b).card)]
    _ = ∑ _p ∈ witnesses a b, (1 : ℝ) / a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ witnesses a b, (1 : ℝ) / p := by
      refine Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le ?_ ?_
      · exact_mod_cast (Finset.mem_filter.mp (hsub hp)).2.1.pos
      · have hpa : p ≤ a - 3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        exact_mod_cast hpa.trans (Nat.sub_le a 3)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- Check successive intervals starting at 100, increasing each endpoint by 40%. -/
private def checkIntervals : ℕ → ℕ → Bool
  | 0, a => 16900 ≤ a
  | n + 1, a =>
    let b := 7 * a / 5
    decide (3 * a ≤ 10 * (witnesses a b).card * a.log2) && checkIntervals n b

private theorem checkIntervals_sound {N : ℕ} (hN : N < 16900) :
    ∀ n a, checkIntervals n a = true → 100 ≤ a → a ≤ N →
      1 / (5 * Real.log N) ≤
        ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
          (1 : ℝ) / p
  | 0, a, h, _, _ => by simp [checkIntervals] at h; omega
  | n + 1, a, h, ha, haN => by
    simp only [checkIntervals, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hNb : N < 7 * a / 5
    · exact interval_bound ha haN hNb h.1
    · exact checkIntervals_sound hN n _ h.2 (by omega) (by omega)

private theorem intervals_checked : checkIntervals 16 100 = true := by decide +kernel

theorem three_mul_primeCounting_le (s : ℕ) (hs : 6 ≤ s) : 3 * Nat.primeCounting s ≤ s + 9 := by
  have h := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl (s - 6)
  rw [show 6 + (s - 6) = s by omega] at h
  have h6 : Nat.primeCounting 6 = 3 := by decide
  have ht : Nat.totient 6 = 2 := by decide
  rw [h6, ht] at h
  omega

theorem centralBinom_le_pow_primeCounting (n : ℕ) (n_large : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (Nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let T := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hf : ∀ p, f p ≤ 2 * n := fun p => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h1 := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have h2 := (Finset.mem_filter.1 hy).2.2
    omega
  have key : n.centralBinom = (∏ x ∈ S, f x) * ∏ x ∈ T, f x := by
    rw [← Finset.prod_union hdisj]
    refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
    apply Finset.prod_subset
    · intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · have h1 := Finset.mem_range.1 (Finset.mem_filter.1 h).1
        rw [Finset.mem_range]; omega
      · exact (Finset.mem_filter.1 h).1
    intro x hx h2x
    by_cases hp : x.Prime
    · have h1 : ¬ x < 2 * n / 3 + 1 := fun h => h2x (Finset.mem_union.2 (Or.inl
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hp⟩)))
      have h2 : ¬ n < x := fun h => h2x (Finset.mem_union.2 (Or.inr
        (Finset.mem_filter.2 ⟨hx, hp, h⟩)))
      have h3 : 2 * n < 3 * x := by omega
      simp only [f]
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large (not_lt.1 h2) h3,
        Nat.pow_zero]
    · simp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hp, Nat.pow_zero]
  rw [key]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ?_
      rw [← Nat.primesLE_card_eq_primeCounting]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Nat.mem_primesLE.2 ⟨h2, (Finset.mem_filter.1 h1).2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
    rw [Finset.prod_const]

theorem inv_five_log_le_sum_inv_primes_of_large (N : ℕ) (hN : 16900 ≤ N) :
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  set U := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hU
  obtain ⟨n, hn⟩ : ∃ n, n = N / 2 := ⟨_, rfl⟩
  set T := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p) with hT
  have hcard : T.card ≤ U.card + 3 := by
    have hsub : T ⊆ U ∪ {N - 2, N - 1, N} := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hx
      rw [Finset.mem_range] at h1
      by_cases h : x + 3 ≤ N
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), h2, by omega, h⟩))
      · refine Finset.mem_union.2 (Or.inr ?_)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    exact Nat.add_le_add_left Finset.card_le_three _
  have h1 := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le_pow_primeCounting n (by omega)
  rw [← hT] at h2
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt N := ⟨_, rfl⟩
  have hs1 : s * s ≤ N := hs ▸ Nat.sqrt_le N
  have hs2 : N < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt N
  have hs3 : 130 ≤ s := by
    by_contra h
    have : s + 1 ≤ 130 := by omega
    have := Nat.mul_le_mul this this
    omega
  obtain ⟨K, hK⟩ : ∃ K, K = Nat.primeCounting (Nat.sqrt (2 * n)) := ⟨_, rfl⟩
  rw [← hK] at h2
  have hK3 : 3 * K ≤ s + 9 := by
    have a : K ≤ Nat.primeCounting s :=
      hK ▸ Nat.monotone_primeCounting (hs ▸ Nat.sqrt_le_sqrt (by omega))
    have b := three_mul_primeCounting_le s (by omega)
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = n - 2 * n / 3 := ⟨_, rfl⟩
  have h3 : 4 ^ m ≤ N ^ (K + U.card + 4) := by
    have hNpos : 1 ≤ N := by omega
    have e : 4 ^ n = 4 ^ m * 4 ^ (2 * n / 3) := by
      rw [← pow_add]; congr 1; omega
    have a1 : (2 * n) ^ K ≤ N ^ K := Nat.pow_le_pow_left (by omega) _
    have a2 : (2 * n) ^ T.card ≤ N ^ (U.card + 3) :=
      (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hNpos hcard)
    have a3 : 4 ^ m * 4 ^ (2 * n / 3) ≤ N ^ (K + U.card + 4) * 4 ^ (2 * n / 3) := by
      rw [← e]
      calc 4 ^ n ≤ n * n.centralBinom := h1.le
        _ ≤ N * (N ^ K * 4 ^ (2 * n / 3) * N ^ (U.card + 3)) :=
          Nat.mul_le_mul (by omega) (h2.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ a1) a2))
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right a3 (by positivity)
  have hNR : (16900 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have h4 : (m : ℝ) * Real.log 4 ≤ (K + U.card + 4) * Real.log N := by
    have : ((4 : ℝ)) ^ m ≤ (N : ℝ) ^ (K + U.card + 4) := by exact_mod_cast h3
    have := Real.log_le_log (by positivity) this
    rw [Real.log_pow, Real.log_pow] at this
    exact_mod_cast this
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hmR : (N : ℝ) ≤ 6 * m + 1 := by
    have : N ≤ 6 * m + 1 := by omega
    exact_mod_cast this
  have hsR : (130 : ℝ) ≤ s := by exact_mod_cast hs3
  have hs1R : (s : ℝ) * s ≤ N := by exact_mod_cast hs1
  have hs2R : (N : ℝ) ≤ (s + 1) * (s + 1) := by exact_mod_cast hs2.le
  have hK3R : 3 * (K : ℝ) ≤ s + 9 := by exact_mod_cast hK3
  have hLle : Real.log N ≤ (s + 1) / 64 + 7.70407 := by
    have b1 : Real.log N ≤ 2 * Real.log (s + 1) := by
      have := Real.log_le_log (by linarith) hs2R
      rw [Real.log_mul (by linarith) (by linarith)] at this
      linarith
    have b2 : Real.log ((s + 1) / 2 ^ 7) ≤ (s + 1) / 2 ^ 7 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (by norm_num), Real.log_pow] at b2
    push_cast at b2
    linarith
  have h5 : (N : ℝ) ≤ U.card * (5 * Real.log N) := by
    have c1 : ((s : ℝ) + 21) * Real.log N ≤ (s + 21) * ((s + 1) / 64 + 7.70407) :=
      mul_le_mul_of_nonneg_left hLle (by linarith)
    have c2 : (m : ℝ) * 1.386294 ≤ m * Real.log 4 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have c3 : 130 * (s : ℝ) ≤ s * s := mul_le_mul_of_nonneg_right hsR (by linarith)
    have c4 : 3 * (K : ℝ) * Real.log N ≤ (s + 9) * Real.log N :=
      mul_le_mul_of_nonneg_right hK3R hL.le
    nlinarith
  calc 1 / (5 * Real.log N) ≤ (U.card : ℝ) * (1 / N) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by linarith)]
        linarith
    _ = ∑ _p ∈ U, (1 : ℝ) / N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨-, hp1, -, hp2⟩ := Finset.mem_filter.1 hp
        have : (0 : ℝ) < p := by exact_mod_cast hp1.pos
        have h' : (p : ℝ) ≤ N := by exact_mod_cast (by omega : p ≤ N)
        exact one_div_le_one_div_of_le this h'

theorem inv_five_log_le_sum_inv_primes :
    ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  intro N hN
  by_cases h : N < 16900
  · exact checkIntervals_sound h 16 100 intervals_checked le_rfl hN
  · exact inv_five_log_le_sum_inv_primes_of_large N (by omega)

end GlobalTheory.PrimeRecip
