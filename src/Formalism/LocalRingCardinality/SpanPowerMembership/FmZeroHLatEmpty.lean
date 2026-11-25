module

public import Formalism.LocalRingCardinality.DataForms
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField Formalism.BasicNotions

section Weights

variable {R : Ranks} (P : HCParam R)

def blkN (R : Ranks) (n : ℕ) : ℕ := (n - R.k) / (R.t + 1)

def wtN (n : ℕ) : ℚ :=
  if h : n < R.k then hcToWeightQ P.u ⟨n, h⟩
  else if hb : blkN R n < R.m then -wG R (P.e ⟨blkN R n, hb⟩) (blkN R n + 1) else 0

def wtQ (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : ℚ :=
  if h : i.1 < R.k then hcToWeightQ P.u ⟨i.1, h⟩
  else -wG R (P.e ⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj i h⟩) ((i.1 - R.k) / (R.t + 1) + 1)

theorem wtQ_eq_wtN (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : wtQ P j hj i = wtN P i.1 := by
  by_cases h : i.1 < R.k
  · simp only [wtQ, wtN, dite_eq_left h]
  · have hb : blkN R i.1 < R.m := R.blk_lt hj i h
    rw [wtQ, wtN, dite_eq_right h, dite_eq_right h, dite_eq_left hb]
    rfl

theorem u_step (i : ℕ) (hi : i + 1 < R.k) : P.u ⟨i + 1, hi⟩ + 1 ≤ P.u ⟨i, by omega⟩ := by
  have hi' : i < R.k - 1 := by omega
  have h1 : P.v ⟨i, hi'⟩ < P.u ⟨i, by omega⟩ := P.u_gt_v ⟨i, hi'⟩
  have h2 : P.u ⟨i + 1, hi⟩ < P.v ⟨i, hi'⟩ := P.v_gt_u ⟨i, hi'⟩
  obtain ⟨a, ha⟩ := P.u_half ⟨i + 1, hi⟩
  obtain ⟨c, hc⟩ := P.u_half ⟨i, by omega⟩
  obtain ⟨b, hb⟩ := P.v_int ⟨i, hi'⟩
  rw [hb, hc] at h1
  rw [hb, ha] at h2
  rw [ha, hc]
  have e1 : (a : ℚ) < b := by linarith
  have e2 : (b : ℚ) < c + 1 := by linarith
  have f1 : a < b := by exact_mod_cast e1
  have f2 : b < c + 1 := by exact_mod_cast e2
  have f3 : ((a : ℚ) + 1) ≤ c := by exact_mod_cast (show a + 1 ≤ c by omega)
  linarith

private theorem wtN_eq_neg_wG_blkN (n : ℕ) (hn : ¬ n < R.k) (hb : blkN R n < R.m) :
    wtN P n = -wG R (P.e ⟨blkN R n, hb⟩) (blkN R n + 1) := by
  unfold wtN
  rw [dite_eq_right hn, dite_eq_left hb]

private theorem neg_wG_le_of_adjacent_blocks (c c' : ℕ) (hc : c < R.m) (hc' : c' < R.m) (h : c' = c ∨ c' = c + 1) :
    -wG R (P.e ⟨c', hc'⟩) (c' + 1) ≤ -wG R (P.e ⟨c, hc⟩) (c + 1) := by
  rcases h with rfl | rfl
  · exact le_rfl
  · have h1 : ((R.t : ℚ) + 3) / 2 ≤ P.e ⟨c + 1, hc'⟩ - P.b ⟨c + 1, hc'⟩ := P.gap_be ⟨c + 1, hc'⟩
    have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨c + 1, hc'⟩ - P.e ⟨c, hc⟩ := P.gap_eb ⟨c, hc⟩ hc'
    simp only [wG]
    push_cast
    linarith

theorem wtN_step (n : ℕ) (hn : n + 1 < R.N R.m) : wtN P (n + 1) ≤ wtN P n := by
  by_cases hn0 : n < R.k
  · by_cases hA : n + 1 < R.k
    · have hs := u_step P n hA
      unfold wtN
      rw [dite_eq_left hA, dite_eq_left hn0]
      simp only [hcToWeightQ, rhoVec]
      push_cast
      linarith
    · have hk : n + 1 = R.k := by omega
      have hm0 : 0 < R.m := by have := R.two_le_m; omega
      have hb : blkN R (n + 1) < R.m := by
        unfold blkN
        rw [show n + 1 - R.k = 0 by omega, Nat.zero_div]
        exact hm0
      have hb0 : blkN R (n + 1) = 0 := by
        unfold blkN
        rw [show n + 1 - R.k = 0 by omega, Nat.zero_div]
      rw [wtN_eq_neg_wG_blkN P (n + 1) hA hb]
      have he : P.e ⟨blkN R (n + 1), hb⟩ = P.e ⟨0, hm0⟩ := by
        congr 1
        exact Fin.ext hb0
      rw [he, hb0]
      have hnk : (⟨R.k - 1, by omega⟩ : Fin R.k) = ⟨n, hn0⟩ := Fin.ext (by show R.k - 1 = n; omega)
      have h1 := P.u_last_gt (by omega) hm0
      rw [hnk] at h1
      have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.e ⟨0, hm0⟩ - P.b ⟨0, hm0⟩ := P.gap_be ⟨0, hm0⟩
      have hnq : (n : ℚ) + 1 = R.k := by exact_mod_cast hk
      unfold wtN
      rw [dite_eq_left hn0]
      simp only [wG, hcToWeightQ, rhoVec]
      push_cast
      linarith
  · have hmn : n + 1 - R.k < R.m * (R.t + 1) := by
      unfold Ranks.N at hn
      omega
    have hb1 : blkN R (n + 1) < R.m := by
      unfold blkN
      exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr hmn
    have hle : blkN R n ≤ blkN R (n + 1) := Nat.div_le_div_right (by omega)
    have hb0 : blkN R n < R.m := lt_of_le_of_lt hle hb1
    have hor : blkN R (n + 1) = blkN R n ∨ blkN R (n + 1) = blkN R n + 1 := by
      unfold blkN
      rw [show n + 1 - R.k = (n - R.k) + 1 by omega, Nat.succ_div]
      split_ifs <;> simp
    rw [wtN_eq_neg_wG_blkN P (n + 1) (by omega) hb1, wtN_eq_neg_wG_blkN P n hn0 hb0]
    exact neg_wG_le_of_adjacent_blocks P _ _ hb0 hb1 hor

theorem wtN_anti {n n' : ℕ} (h : n ≤ n') (hn' : n' < R.N R.m) : wtN P n' ≤ wtN P n := by
  revert hn'
  induction n', h using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ q hq ih =>
    intro hq'
    exact le_trans (wtN_step P q hq') (ih (by omega))

theorem N_mono {j : ℕ} (hj : j ≤ R.m) : R.N j ≤ R.N R.m := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _

theorem wtQ_anti (j : ℕ) (hj : j ≤ R.m) : Antitone (wtQ P j hj) := by
  intro a b hab
  rw [wtQ_eq_wtN, wtQ_eq_wtN]
  exact wtN_anti P hab (lt_of_lt_of_le b.2 (N_mono hj))

theorem wtQ_int (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : ∃ z : ℤ, wtQ P j hj i = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hk : (R.k : ℚ) = a + a := by exact_mod_cast ha
  have ht : (R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  by_cases h : i.1 < R.k
  · obtain ⟨z, hz⟩ := P.u_half ⟨i.1, h⟩
    refine ⟨z + 1 - a + i.1, ?_⟩
    rw [wtQ, dite_eq_left h]
    simp only [hcToWeightQ, rhoVec, hz]
    rw [hk]
    push_cast
    ring
  · obtain ⟨z, hz⟩ := P.e_int ⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj i h⟩
    refine ⟨-z + a + (2 * (((i.1 - R.k) / (R.t + 1) : ℕ) : ℤ) + 1) * (c + 1), ?_⟩
    rw [wtQ, dite_eq_right h]
    simp only [wG, hz]
    generalize (i.1 - R.k) / (R.t + 1) = B
    rw [hk, ht]
    push_cast
    ring

def lamOf (j : ℕ) : DomWeight (R.N j) :=
  if hj : j ≤ R.m then ⟨fun i => ⌊wtQ P j hj i⌋, fun _ _ hii => Int.floor_mono (wtQ_anti P j hj hii)⟩
  else ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

theorem lamOf_eq (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : ((lamOf P j).w i : ℚ) = wtQ P j hj i := by
  obtain ⟨z, hz⟩ := wtQ_int P j hj i
  simp only [lamOf, dite_eq_left hj, hz, Int.floor_intCast]

end Weights

def fmZeroHLat (K : Type) [Field K] [NumberField K] [StarRing K] : HLat K where
  V := Fin 0 → K
  ι := Fin 0
  b := Pi.basisFun K (Fin 0)
  X := fun _ => 0
  L := ⊤

instance fmZeroHLat_sub (K : Type) [Field K] [NumberField K] [StarRing K] :
    Subsingleton (fmZeroHLat K).V := inferInstanceAs (Subsingleton (Fin 0 → K))

instance fmZeroHLat_empty (K : Type) [Field K] [NumberField K] [StarRing K] :
    IsEmpty (fmZeroHLat K).ι := inferInstanceAs (IsEmpty (Fin 0))

theorem fmZeroHLat_good (K : Type) [Field K] [NumberField K] [StarRing K] : (fmZeroHLat K).Good := by
  unfold HLat.Good
  refine ⟨fun v => ?_, ?_, Subsingleton.elim _ _⟩
  · rw [Matrix.det_isEmpty]
    exact isUnit_one
  · rw [Subsingleton.elim (fmZeroHLat K).L ⊥]
    exact Submodule.fg_bot

theorem fmZeroHLat_maj (K : Type) [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)
    (x y : (fmZeroHLat K).V) :
    Formalism.HermitianLatticesTheory.majAt (fmZeroHLat K).b (fmZeroHLat K).X v x y = 0 := by
  unfold Formalism.HermitianLatticesTheory.majAt
  exact Fintype.sum_empty _

section Forms

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (hTau : Fintype.card Tau = R.f)
  {hc : Tau → HCParam R} (C : ColumnChain R Tau hc) [hE : ∀ i, IsEmpty (C.cls i)]
  (A : ColumnsAtT R C) (P : PeriodMap R C)

end Forms

end Formalism.BasicNotions.Examples₂
