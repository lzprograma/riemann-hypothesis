module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NumRho

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Num

variable {ε : Fin n → Bool}

private theorem inner_toLp (u v : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = dot u v := by
  simp [dot, PiLp.inner_apply, mul_comm]

private theorem norm_sq_toLp (u : Fin n → ℝ) : ‖WithLp.toLp 2 u‖ ^ 2 = nsq u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [nsq, dot, sq]

private theorem norm_toLp (u : Fin n → ℝ) : ‖WithLp.toLp 2 u‖ = √(nsq u) := by
  rw [← norm_sq_toLp, Real.sqrt_sq (norm_nonneg _)]

private theorem pq_facts {a b : Fin n} (hε : ε a ≠ ε b) :
    1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) ∧ (pOf ε : ℝ) + (qOf ε : ℝ) = n := by
  have hsum : pOf ε + qOf ε = n := by
    simpa [pOf, qOf] using Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  have hp : ∃ c, ε c = true := by
    cases ha : ε a
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
    · exact ⟨a, ha⟩
  have hq : ∃ c, ε c = false := by
    cases ha : ε a
    · exact ⟨a, ha⟩
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  have h1 : 1 ≤ pOf ε := Finset.card_pos.mpr ⟨c, by simp [hc]⟩
  have h2 : 1 ≤ qOf ε := Finset.card_pos.mpr ⟨d, by simp [hd]⟩
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast hsum⟩

theorem gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨hp, hq, hn⟩ := pq_facts hε
  have hm := mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hq)
  have key : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hm]
  constructor
  · nlinarith [sq_nonneg ((n : ℝ) - 2)]
  · nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem sch_gap {lam : Fin n → ℝ} (hgap : StdGap ε lam) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b) := by
  obtain ⟨hanti, h, hg, hbig⟩ := hgap
  have h1 := hg a b hε
  have hlt : lam b < lam a := hanti hab
  rw [abs_of_pos (sub_pos.2 hlt)] at h1
  rw [numRho_dot_root_right]
  linarith [two_dot_rhoC_rhoN_le ε]

theorem crossVal_pos {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 * (h - n + 1) ≤
      casValK ε (lowK ε lam + root a b) - n - casValK ε (lowK ε lam) := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_lt hab), ← inner_toLp, WithLp.toLp_add,
    inner_add_left, inner_toLp, inner_toLp, numRho_dot_root_right]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  linarith [dot_rhoN_root_ge hab hε]

theorem crossVal_neg {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    casValK ε (lowK ε lam + root b a) - n - casValK ε (lowK ε lam) ≤ -2 * h - 2 := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_gt hab), ← inner_toLp, WithLp.toLp_add,
    inner_add_left, inner_toLp, inner_toLp, numRho_dot_root_right, numRho_dot_root_right]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  rw [numRho_dot_root_right] at h2
  linarith

theorem isNCSum_zero {ν : Fin n → ℝ} : IsNCSum ε 0 ν ↔ ν = 0 := by
  constructor
  · rintro ⟨γ, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩

theorem isNCSum_succ_exists {k : ℕ} {ν : Fin n → ℝ} (hν : IsNCSum ε (k + 1) ν) :
    ∃ a b : Fin n, ε a ≠ ε b := by
  obtain ⟨γ, hγ, -⟩ := hν
  exact ⟨_, _, hγ 0⟩

theorem vogan_num {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  obtain ⟨hg1, hg2⟩ := gap_gt (hγ ⟨0, hj⟩) hbig
  have hρ : -((j : ℝ) * (((n : ℝ) - 2) / 2)) ≤ dot (rhoC ε) (∑ i, root (γ i).1 (γ i).2) := by
    rw [← inner_toLp, WithLp.toLp_sum, inner_sum]
    have : ∑ _i : Fin j, -(((n : ℝ) - 2) / 2) ≤
        ∑ i, inner ℝ (WithLp.toLp 2 (rhoC ε)) (WithLp.toLp 2 (root (γ i).1 (γ i).2)) := by
      apply Finset.sum_le_sum
      intro i _
      have := abs_dot_root_rhoC_le (ε := ε) (hγ i)
      rw [real_inner_comm, inner_toLp]
      linarith [neg_abs_le (dot (root (γ i).1 (γ i).2) (rhoC ε))]
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] using this
  rw [casValK_add] at hc
  have e2 : Λ + (2 : ℝ) • rhoC ε = (Λ + rhoC ε) + rhoC ε := by rw [two_smul]; abel
  have e3 : Λ + (∑ i, root (γ i).1 (γ i).2) + (2 : ℝ) • rhoC ε =
      ((Λ + rhoC ε) + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by rw [two_smul]; abel
  rw [e2, e3, ← norm_sq_toLp (((Λ + rhoC ε) + rhoC ε) + _), WithLp.toLp_add, norm_add_sq_real,
    norm_sq_toLp, norm_sq_toLp, WithLp.toLp_add, inner_add_left, inner_toLp, inner_toLp]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpos : 0 ≤ 2 * h - 3 * (n : ℝ) + 4 := by linarith
  nlinarith [mul_nonneg hj0 hpos]

theorem degree_num {Λ ν : Fin n → ℝ} {j k : ℕ} (hjk : j ≤ k) (hν : IsNCSum ε j ν) :
    casValK ε (Λ + ν) ≤ (√(nsq (Λ + rhoC ε)) + √2 * k) ^ 2 - nsq (rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  have hs : ‖WithLp.toLp 2 (∑ i, root (γ i).1 (γ i).2)‖ ≤ √2 * k := by
    rw [WithLp.toLp_sum]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i, ‖WithLp.toLp 2 (root (γ i).1 (γ i).2)‖ = √2 := fun i => by
      rw [norm_toLp, nsq_root (fun e => hγ i (by rw [e]))]
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (Real.sqrt_nonneg 2)
  unfold casValK
  have e : Λ + (∑ i, root (γ i).1 (γ i).2) + rhoC ε =
      (Λ + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by
    abel
  rw [e, ← norm_sq_toLp]
  have h1 : ‖WithLp.toLp 2 ((Λ + rhoC ε) + ∑ i, root (γ i).1 (γ i).2)‖ ≤
      √(nsq (Λ + rhoC ε)) + √2 * k := by
    rw [WithLp.toLp_add, ← norm_toLp (Λ + rhoC ε)]
    exact (norm_add_le _ _).trans (by linarith)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith

end Num

end ReciprocityTheory.ChartRestriction.DS
