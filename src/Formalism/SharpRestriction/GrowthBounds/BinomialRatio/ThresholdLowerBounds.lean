module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Transported

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem numSeg_le_card {n' : ℕ} (TT : Finset (Fin n')) : numSeg TT ≤ TT.card := by
  unfold numSeg evenTops
  rw [Finset.length_sort]
  exact Finset.card_filter_le _ _

theorem error_ratio_le_epsilon {p k N1 La Q c a b' CE1 CE2 : ℝ} (hk : 1 ≤ k) (hp : k ^ 2 ≤ p) (hN1 : 1 ≤ N1) (hLa : 1 ≤ La)
    (hQ : 1 ≤ Q) (hb : 0 < b') (hab : k * b' ≤ a) (hHc : k ^ 3 * Q ^ 2 * c ≤ b')
    (hHb : k ^ 3 * Q ≤ b') (h1 : 0 ≤ CE1) (h2 : 0 ≤ CE2) (hk2 : 4 * CE1 + CE2 + 1 ≤ k) :
    errorTermBound CE1 CE2 p k N1 Q c a b' La / a + Q / a ≤ N1 * La / k := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hkne : k ≠ 0 := hk0.ne'
  have hksq : 0 < k ^ 2 := pow_pos hk0 2
  have hkp : k ≤ p := (le_self_pow₀ hk (Nat.succ_ne_zero 1 : (2 : ℕ) ≠ 0)).trans hp
  have hp0 : 0 < p := hk0.trans_le hkp
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hk0 hb) hab
  have hLa0 : 0 ≤ La := zero_le_one.trans hLa
  have hN10 : 0 ≤ N1 := zero_le_one.trans hN1
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hNL : 1 ≤ N1 * La := one_le_mul_of_one_le_of_one_le hN1 hLa
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = N1 * La / k ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (mul_nonneg hN10 hLa0) hksq.le
  have hAk : A * k ^ 2 = N1 * La := by rw [hA, div_mul_cancel₀ _ hksq.ne']
  have hAk' : a * A * k ^ 2 = a * (N1 * La) := by rw [mul_assoc, hAk]
  have haA : 0 ≤ a * A := mul_nonneg ha.le hA0
  have hNLa : a * 1 ≤ a * (N1 * La) := mul_le_mul_of_nonneg_left hNL ha.le
  have hAk1 : b' ≤ a * A * k := by
    have h : k * b' ≤ k * (a * A * k) := by linarith only [hab, hNLa, hAk']
    exact le_of_mul_le_mul_left h hk0
  have t1 : a / p ^ 2 ≤ a * A := by
    rw [div_le_iff₀ (pow_pos hp0 2)]
    have hkp2 : k ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hk0.le hkp 2
    linarith only [hNLa, hAk', mul_le_mul_of_nonneg_left hkp2 haA]
  have t2 : b' / p ≤ a * A := by
    rw [div_le_iff₀ hp0]
    linarith only [hAk1, mul_le_mul_of_nonneg_left hkp haA]
  have t3 : La * N1 * a / (p * k) ≤ a * A := by
    rw [div_le_iff₀ (mul_pos hp0 hk0)]
    have hkk : k * k ≤ p * k := mul_le_mul_of_nonneg_right hkp hk0.le
    linarith only [hAk', mul_le_mul_of_nonneg_left hkk haA]
  have t4 : La * b' / k ≤ a * A := by
    rw [div_le_iff₀ hk0]
    have h4a : La * (k * b') ≤ La * a := mul_le_mul_of_nonneg_left hab hLa0
    have h4b : La * a * 1 ≤ La * a * N1 := mul_le_mul_of_nonneg_left hN1 (mul_nonneg hLa0 ha.le)
    have h : k * (La * b') ≤ k * (a * A * k) := by linarith only [h4a, h4b, hAk']
    exact le_of_mul_le_mul_left h hk0
  have t5 : k ^ 2 * N1 * Q ^ 2 * c ≤ a * A := by
    have h5a : k ^ 3 * Q ^ 2 * c * k ≤ b' * k := mul_le_mul_of_nonneg_right hHc hk0.le
    have h5b : a * 1 ≤ a * La := mul_le_mul_of_nonneg_left hLa ha.le
    have h5c : N1 * (k ^ 3 * Q ^ 2 * c * k) ≤ N1 * (a * La) :=
      mul_le_mul_of_nonneg_left (by linarith only [h5a, h5b, hab]) hN10
    have h : k ^ 2 * (k ^ 2 * N1 * Q ^ 2 * c) ≤ k ^ 2 * (a * A) := by linarith only [h5c, hAk']
    exact le_of_mul_le_mul_left h hksq
  have t6 : Q ≤ a * A := by
    have h6a : k * (k ^ 3 * Q) ≤ k * b' := mul_le_mul_of_nonneg_left hHb hk0.le
    have hk2ge : 1 ≤ k ^ 2 := one_le_pow₀ hk
    have h6b : k ^ 2 * 1 ≤ k ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_left hk2ge hksq.le
    have h6c := mul_le_mul_of_nonneg_left h6b hQ0
    have h : k ^ 2 * Q ≤ k ^ 2 * (a * A) := by linarith only [h6a, h6c, hab, hNLa, hAk']
    exact le_of_mul_le_mul_left h hksq
  rw [← add_div, div_le_iff₀ ha]
  unfold errorTermBound
  have s1 : CE1 * (a / p ^ 2 + b' / p + La * N1 * a / (p * k) + La * b' / k) ≤ CE1 * (4 * (a * A)) :=
    mul_le_mul_of_nonneg_left (by linarith only [t1, t2, t3, t4]) h1
  have s2 : CE2 * (k ^ 2 * N1 * Q ^ 2 * c) ≤ CE2 * (a * A) := mul_le_mul_of_nonneg_left t5 h2
  have s3 : (4 * CE1 + CE2 + 1) * (a * A) ≤ k * (a * A) := mul_le_mul_of_nonneg_right hk2 haA
  have s4 : k * (a * A) = N1 * La / k * a := by
    have h := (eq_div_iff hkne).2 (show (A * k) * k = N1 * La by
      simpa only [mul_assoc, ← pow_two] using hAk)
    rw [mul_comm k, mul_assoc, h, mul_comm a]
  linarith only [s1, s2, t6, s3, s4]

def T2 (CE1 CE2 Cc H : ℝ) : ℝ := 1000 * (CE1 + CE2 + 1) * (Cc + 1) * H

theorem chordCoeffCubic_inversionDenom_inv {CE1 CE2 Cc H : ℝ} (hCc : 0 ≤ Cc) (h1 : 1 ≤ CE1) (h2 : 1 ≤ CE2) (hH : 1 ≤ H) :
    1000 ≤ T2 CE1 CE2 Cc H ∧ 4 * CE1 + CE2 + 1 ≤ T2 CE1 CE2 Cc H ∧ 2 * Cc * H ≤ T2 CE1 CE2 Cc H ∧
      H ≤ T2 CE1 CE2 Cc H := by
  unfold T2
  have hP : 3 ≤ CE1 + CE2 + 1 := by linarith only [h1, h2]
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hCH : 0 ≤ Cc * H := mul_nonneg hCc hH0
  have hM1 : 1 ≤ (Cc + 1) * H :=
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left hCc) hH
  have ha : (CE1 + CE2 + 1) * 1 ≤ (CE1 + CE2 + 1) * ((Cc + 1) * H) :=
    mul_le_mul_of_nonneg_left hM1 (by linarith only [hP])
  have hh : H ≤ (Cc + 1) * H := by rw [add_mul, one_mul]; exact le_add_of_nonneg_left hCH
  have hc : Cc * H ≤ (Cc + 1) * H := by rw [add_mul, one_mul]; exact le_add_of_nonneg_right hH0
  have hb : 3 * ((Cc + 1) * H) ≤ (CE1 + CE2 + 1) * ((Cc + 1) * H) :=
    mul_le_mul_of_nonneg_right hP (zero_le_one.trans hM1)
  exact ⟨by linarith only [ha, hP], by linarith only [ha, h1, h2],
    by linarith only [hb, hc, hCH], by linarith only [hb, hh, hH0]⟩


theorem std_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc H : ℝ} (hCc : 0 ≤ Cc) (hC0 : 1 ≤ C0) (h1 : 1 ≤ CE1) (h2 : 1 ≤ CE2)
    (hH : 1 ≤ H) (t1 : T2 CE1 CE2 Cc H ≤ CYb) (t2 : T2 CE1 CE2 Cc H ≤ Cde) (t3 : T2 CE1 CE2 Cc H ≤ Ck)
    (t4 : T2 CE1 CE2 Cc H ≤ CD) (t5 : T2 CE1 CE2 Cc H ≤ Cb) {X : Loc} (hD : D1num X)
    (hI : HIext C0 CYb Cde Ck CD Cb X) (hc : CBound Cc X) : Std C0 Cde CE1 CE2 H X := by
  have one_le_mul {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y :=
    one_le_mul_of_one_le_of_one_le hx hy
  obtain ⟨hT1, hT2, hT3, hT4⟩ := chordCoeffCubic_inversionDenom_inv hCc h1 h2 hH
  unfold D1num at hD
  obtain ⟨hpP, hp5, hn2, hnEv⟩ := hD
  unfold HIext WindowHypotheses InWin at hI
  obtain ⟨⟨hY1, hpk, _hEv, hseg, hsegB, hN1, hm, hLaNY, hb, hbl, hbh, _hYbw, _hw2, hCYb, hYbk, hab16,
    hde, hpab, hCk, hband, hccl0, _hccl, hDLP, hcs, hCb⟩, hwA, hwB⟩ := hI
  unfold CBound at hc

  have hkdef : X.k = (X.m : ℝ) + 1 := rfl
  have hmR : 2 * (X.N1 : ℝ) + 2 ≤ X.m := by exact_mod_cast hm
  have hN1R : (1 : ℝ) ≤ X.N1 := by exact_mod_cast hN1
  have sq_level_le_degree : 2 * (X.N1 : ℝ) + 3 ≤ X.k := by rw [hkdef]; linarith only [hmR]
  have hk1 : (1 : ℝ) ≤ X.k := by linarith only [sq_level_le_degree, hN1R]
  have hk0 : 0 < X.k := zero_lt_one.trans_le hk1
  have hkne : X.k ≠ 0 := hk0.ne'
  have hp5R : (5 : ℝ) ≤ X.p := by exact_mod_cast hp5
  have hp1 : (1 : ℝ) ≤ X.p := by linarith only [hp5R]
  have hQ1 : 1 ≤ X.Q := one_le_pow₀ hp1
  have hQ0 : 0 ≤ X.Q := zero_le_one.trans hQ1
  have hcard : 2 ≤ X.TT.card := le_trans hseg (numSeg_le_card _)
  have hN2 : (2 : ℝ) ≤ X.N := by show (2 : ℝ) ≤ (X.TT.card : ℝ); exact_mod_cast hcard
  have hN_one : 1 ≤ X.N := by linarith only [hN2]
  have hN0 : 0 ≤ X.N := zero_le_one.trans hN_one
  have hY0 : 0 ≤ X.Y := zero_le_one.trans hY1
  have hbne : X.b' ≠ 0 := hb.ne'
  have hYb1 : 1 ≤ X.Yb := by linarith only [hT1, t1, hCYb]
  have hY2 : 1 ≤ X.Y ^ 2 := one_le_pow₀ hY1

  have ha1 : (1 : ℝ) ≤ X.a := by
    have hne : X.a ≠ 0 := by
      intro h
      rw [h, Nat.cast_zero, zero_div] at hpab
      linarith only [hp5R, hpab]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hlogb : 0 ≤ Real.logb X.p X.a := Real.logb_nonneg (by linarith only [hp5R]) ha1
  have hCD1 : 1 ≤ CD := by linarith only [hT1, t4]
  have hDLP0 : 0 ≤ X.DLP := le_trans (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hCD1) hN0)
    (sq_nonneg _)) (add_nonneg (pow_nonneg (Nat.cast_nonneg _) 5) (pow_nonneg hk0.le 3))) hlogb) hDLP
  have hNc : 0 ≤ X.N * X.ccl := mul_nonneg hN0 hccl0
  have hnc : 0 ≤ (X.n' : ℝ) * X.ccl := mul_nonneg (Nat.cast_nonneg _) hccl0
  have hF : 8 * (X.DLP + 1) ≤ X.cs + X.N * X.ccl + X.n' * X.ccl := by
    linarith only [hcs, hNc, hnc]
  have hF1 : 1 ≤ X.cs + X.N * X.ccl + X.n' * X.ccl := by linarith only [hDLP0, hF]
  have hCb1 : 1 ≤ Cb := by linarith only [hT1, t5]
  have hb1 : 1 ≤ X.b' := hCb.trans' <|
    one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_mul hCb1 (one_le_pow₀ hk1)) hN_one)
      (one_le_pow₀ hQ1)) hF1) hY1
  have ha5 : (5 : ℝ) ≤ X.a := by
    have h := hpab
    rw [lt_div_iff₀ hb] at h
    have hpb := mul_le_mul hp5R hb1 (by norm_num) (zero_le_one.trans hp1)
    linarith only [h, hpb]

  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith only [h]
  have hl4 : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hla : Real.log ((2 : ℝ) ^ 2) ≤ Real.log X.a := Real.log_le_log (by norm_num)
    (by rw [show (2 : ℝ) ^ 2 = 4 by norm_num]; linarith only [ha5])
  have hloga : 1 ≤ Real.log X.a := by linarith only [hla, hl4, hl2]

  have hLadef : X.La C0 = C0 * (X.N1 : ℝ) ^ 2 * Real.log X.a := rfl
  have hLa1 : 1 ≤ X.La C0 := by
    rw [hLadef]
    exact one_le_mul (one_le_mul hC0 (one_le_pow₀ hN1R)) hloga
  have hLa0 : 0 ≤ X.La C0 := zero_le_one.trans hLa1

  have h16 := hab16
  rw [le_div_iff₀ hb] at h16
  have hm1 : 1 ≤ X.Y * X.Yb * X.N * Real.log X.a :=
    one_le_mul (one_le_mul (one_le_mul hY1 hYb1) hN_one) hloga
  have hP1 : 1 ≤ X.Y ^ 2 * X.Yb * X.N * X.La C0 * Real.log X.a :=
    one_le_mul (one_le_mul (one_le_mul (one_le_mul hY2 hYb1) hN_one) hLa1) hloga
  have hkb : X.k * X.b' ≤ X.a := by
    have hprod := mul_le_mul_of_nonneg_left hP1 (mul_nonneg hk0.le hb.le)
    linarith only [hprod, h16]
  have hYLa : 0 ≤ X.Y * X.La C0 := mul_nonneg hY0 hLa0
  have hK1 : X.Y * X.La C0 * 1 ≤ X.Y * X.La C0 * (X.Y * X.Yb * X.N * Real.log X.a) :=
    mul_le_mul_of_nonneg_left hm1 hYLa
  have hK2 : 2 * (X.Y * X.La C0 * X.b') ≤ X.k * (X.Y * X.La C0 * X.b') :=
    mul_le_mul_of_nonneg_right (by linarith only [sq_level_le_degree, hN1R]) (mul_nonneg hYLa hb.le)
  have hK3 : X.k * (X.Y * X.La C0 * 1) * X.b' ≤
      X.k * (X.Y * X.La C0 * (X.Y * X.Yb * X.N * Real.log X.a)) * X.b' :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK1 hk0.le) hb.le
  have hKA : 2 * X.Y * X.La C0 * X.b' ≤ X.a := by linarith only [hK2, hK3, h16]

  have hLaN : 2 * X.N * X.La C0 ≤ X.k := by
    have hprod := mul_le_mul_of_nonneg_right hYb1 (mul_nonneg hN0 hLa0)
    linarith only [hprod, hYbk]
  have hv0 : 0 ≤ (X.N1 : ℝ) * X.La C0 / X.k := div_nonneg (mul_nonneg (zero_le_one.trans hN1R) hLa0) hk0.le
  have hr0 : 0 ≤ (X.bh - X.bl) / X.b' := div_nonneg (sub_nonneg.mpr (hbl.trans hbh)) hb.le
  have ed : X.de C0 Cde = Cde * ((X.N1 : ℝ) * X.La C0 / X.k) + 2 * ((X.bh - X.bl) / X.b') := by
    rw [Loc.de, mul_assoc Cde, mul_div_assoc Cde, mul_div_assoc (2 : ℝ)]
  have hCv : 1000 * ((X.N1 : ℝ) * X.La C0 / X.k) ≤ Cde * ((X.N1 : ℝ) * X.La C0 / X.k) :=
    mul_le_mul_of_nonneg_right (by linarith only [hT1, t2]) hv0
  have hLaK : 40 * (X.N1 : ℝ) * X.La C0 / X.k ≤ X.de C0 Cde := by
    rw [mul_assoc (40 : ℝ), mul_div_assoc (40 : ℝ), ed]
    linarith only [hCv, hv0, hr0]
  have eb : be X C0 = (X.bh - X.bl) / X.b' + 2 * (X.La C0 / X.k) := by simp only [be, mul_div_assoc]
  have hu0 : 0 ≤ X.La C0 / X.k := div_nonneg hLa0 hk0.le
  have hu : X.La C0 / X.k * 1 ≤ X.La C0 / X.k * X.N1 := mul_le_mul_of_nonneg_left hN1R hu0
  rw [mul_one, mul_comm (X.La C0 / X.k), ← mul_div_assoc] at hu
  have hbeLe : be X C0 ≤ X.de C0 Cde / 2 - 18 * X.N1 * X.La C0 / X.k := by
    rw [eb, ed, mul_assoc (18 : ℝ), mul_div_assoc (18 : ℝ)]
    linarith only [hCv, hv0, hu]
  have hbe0 : 0 ≤ be X C0 := by
    rw [eb]
    exact add_nonneg hr0 (mul_nonneg (by norm_num) hu0)
  have hkY : 0 < X.k * X.Y := mul_pos hk0 (zero_lt_one.trans_le hY1)
  have eJ0 : X.J0 C0 = X.La C0 * X.b' / X.k := rfl
  have hJ0 : 0 ≤ X.J0 C0 := div_nonneg (mul_nonneg hLa0 hb.le) hk0.le
  have hJ : 2 * X.J0 C0 ≤ X.a / (X.k * X.Y) := by
    rw [le_div_iff₀ hkY]
    have eJ : 2 * X.J0 C0 * (X.k * X.Y) = 2 * X.Y * X.La C0 * X.b' := by
      rw [eJ0, ← mul_assoc, mul_assoc (2 : ℝ), div_mul_cancel₀ _ hkne]
      ring
    exact eJ.trans_le hKA
  have hwinA : ∀ s ∈ X.TT, (X.a : ℝ) ≤ X.aT s ∧ (X.aT s : ℝ) ≤ X.a * (1 + 2 / (X.k * X.Y)) := by
    intro s hs
    obtain ⟨h1s, h2s⟩ := hwA s hs
    refine ⟨h1s, ?_⟩
    have e : (X.a : ℝ) * (1 + 2 / (X.k * X.Y)) = X.a + X.a / (X.k * X.Y) + X.a / (X.k * X.Y) := by ring
    linarith only [e, h2s, hJ]
  have hbe_mul : X.b' * be X C0 = X.bh - X.bl + 2 * X.J0 C0 := by
    rw [eb, mul_add, mul_comm X.b' ((X.bh - X.bl) / X.b'), div_mul_cancel₀ _ hbne, eJ0]
    ring
  have hwinB : ∀ s ∈ X.TT, X.b' * (1 - be X C0) ≤ X.bT s ∧ (X.bT s : ℝ) ≤ X.b' * (1 + be X C0) := by
    intro s hs
    obtain ⟨h1s, h2s⟩ := hwB s hs
    rw [mul_sub, mul_add, mul_one, hbe_mul]
    exact ⟨by linarith only [hbh, h1s, hJ0], by linarith only [hbl, h2s]⟩
  have hab : X.k * X.Y ^ 2 * X.N * X.La C0 * Real.log X.a ≤ X.a / X.b' := by
    have hq0 : 0 ≤ X.k * X.Y ^ 2 * X.N * X.La C0 * Real.log X.a :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hk0.le (sq_nonneg _)) hN0) hLa0) (zero_le_one.trans hloga)
    have hprod := mul_le_mul_of_nonneg_left hYb1 hq0
    linarith only [hprod, hab16]

  have hz : 0 ≤ X.N * Real.logb X.p X.a := mul_nonneg hN0 hlogb
  have hL1 : X.N * Real.logb X.p X.a * X.k ≤ X.N * Real.logb X.p X.a * X.k ^ 3 :=
    mul_le_mul_of_nonneg_left (le_self_pow₀ hk1 (Nat.succ_ne_zero 2)) hz
  have hs0 : 0 ≤ (X.N1 : ℝ) ^ 5 + X.k ^ 3 := add_nonneg (pow_nonneg (Nat.cast_nonneg _) 5) (pow_nonneg hk0.le 3)
  have hL2 : X.N * Real.logb X.p X.a * X.k ^ 3 ≤ X.N * Real.logb X.p X.a * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg (Nat.cast_nonneg X.N1) 5)) hz
  have hCY : 1 ≤ CD * X.Y ^ 2 := one_le_mul hCD1 hY2
  have hL3 : X.N * Real.logb X.p X.a * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) * 1 ≤
      X.N * Real.logb X.p X.a * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) * (CD * X.Y ^ 2) :=
    mul_le_mul_of_nonneg_left hCY (mul_nonneg hz hs0)
  have hNkL : X.N * X.k * Real.logb X.p X.a ≤ X.DLP := by linarith only [hL1, hL2, hL3, hDLP]
  have hF0 : 0 ≤ X.cs + X.N * X.ccl + X.n' * X.ccl := zero_le_one.trans hF1
  have hcF : (X.c : ℝ) ≤ Cc * (2 * (X.cs + X.N * X.ccl + X.n' * X.ccl)) :=
    le_trans hc (mul_le_mul_of_nonneg_left (by linarith only [hNkL, hDLP0, hF]) hCc)
  have hHc' : H * X.c ≤ Cb * (X.cs + X.N * X.ccl + X.n' * X.ccl) := by
    have ha' := mul_le_mul_of_nonneg_left hcF (zero_le_one.trans hH)
    have h2CH : 2 * Cc * H ≤ Cb := le_trans hT3 t5
    have hb' := mul_le_mul_of_nonneg_right h2CH hF0
    linarith only [ha', hb']
  have hG : 0 ≤ X.k ^ 3 * X.N * X.Q ^ 4 * X.Y :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hk0.le 3) hN0) (pow_nonneg hQ0 4)) hY0
  have hHcF : H * X.k ^ 3 * X.N * X.Q ^ 4 * X.c * X.Y ≤ X.b' := by
    have hprod := mul_le_mul_of_nonneg_left hHc' hG
    linarith only [hprod, hCb]
  have hHbF : H * X.k ^ 3 * X.N * X.Q ^ 4 * X.Y ≤ X.b' := by
    have hHCb : H ≤ Cb := le_trans hT4 t5
    have hHF : H * 1 ≤ Cb * (X.cs + X.N * X.ccl + X.n' * X.ccl) :=
      mul_le_mul hHCb hF1 zero_le_one (zero_le_one.trans hCb1)
    have hprod := mul_le_mul_of_nonneg_left hHF hG
    linarith only [hprod, hCb]
  have hCE1 : (0 : ℝ) ≤ CE1 := zero_le_one.trans h1
  have hCE2 : (0 : ℝ) ≤ CE2 := zero_le_one.trans h2
  have hE0 : 0 ≤ X.E0 C0 CE1 CE2 := by
    unfold Loc.E0 errorTermBound
    refine add_nonneg (mul_nonneg hCE1 (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_)) ?_
    · exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    · exact div_nonneg hb.le (Nat.cast_nonneg _)
    · exact div_nonneg (mul_nonneg (mul_nonneg hLa0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) hk0.le)
    · exact div_nonneg (mul_nonneg hLa0 hb.le) hk0.le
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCE2 (sq_nonneg _)) (Nat.cast_nonneg _))
        (sq_nonneg _)) (Nat.cast_nonneg _)

  have hp' : X.k ^ 2 ≤ (X.p : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)
    linarith only [hprod, hpk]
  have hQ2 : 1 ≤ X.Q ^ 2 := one_le_pow₀ hQ1
  have hHc3 : X.k ^ 3 * X.Q ^ 2 * X.c ≤ X.b' := by
    have hf : 1 ≤ H * X.N * X.Q ^ 2 * X.Y := one_le_mul (one_le_mul (one_le_mul hH hN_one) hQ2) hY1
    have hg : 0 ≤ X.k ^ 3 * X.Q ^ 2 * (X.c : ℝ) :=
      mul_nonneg (mul_nonneg (pow_nonneg hk0.le 3) (sq_nonneg _)) (Nat.cast_nonneg _)
    have hprod := mul_le_mul_of_nonneg_left hf hg
    linarith only [hprod, hHcF]
  have hHb3 : X.k ^ 3 * X.Q ≤ X.b' := by
    have hf : 1 ≤ H * X.N * X.Q ^ 3 * X.Y :=
      one_le_mul (one_le_mul (one_le_mul hH hN_one) (one_le_pow₀ hQ1)) hY1
    have hg : 0 ≤ X.k ^ 3 * X.Q := mul_nonneg (pow_nonneg hk0.le 3) hQ0
    have hprod := mul_le_mul_of_nonneg_left hf hg
    linarith only [hprod, hHbF]
  have hk2' : 4 * CE1 + CE2 + 1 ≤ X.k := by
    have hNL : 1 ≤ X.N * X.La C0 ^ 2 := one_le_mul hN_one (one_le_pow₀ hLa1)
    have hCk0 : 0 ≤ Ck := by linarith only [hT1, t3]
    have hprod := mul_le_mul (hT2.trans t3) hNL zero_le_one hCk0
    linarith only [hprod, hCk]
  have hN5 := error_ratio_le_epsilon hk1 hp' hN1R hLa1 hQ1 hb hkb hHc3 hHb3 hCE1 hCE2 hk2'
  exact ⟨hpP, hp5, hn2, hnEv, hY1, hpk, sq_level_le_degree, hN1, hseg, hN2, hsegB, hb, hloga, hLa1, hLaNY, hLaN,
    hLaK, hde, hbeLe, hbe0, hwinA, hwinB, hpab, hab, hband, hHcF, hHbF, hE0, hN5⟩

namespace Std

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

theorem one_le_level_alt (S : Std C0 Cde CE1 CE2 H X) : (1 : ℝ) ≤ X.N1 := by
  exact_mod_cast S.N1pos

theorem k5 (S : Std C0 Cde CE1 CE2 H X) : 5 ≤ X.k := by
  have h := S.N1k
  have h' := one_le_level_alt S
  linarith only [h, h']

theorem p5r (S : Std C0 Cde CE1 CE2 H X) : (5 : ℝ) ≤ X.p := by
  exact_mod_cast S.p5

theorem Q1 (S : Std C0 Cde CE1 CE2 H X) : 1 ≤ X.Q := by
  show (1 : ℝ) ≤ (X.p : ℝ) ^ X.G'
  exact one_le_pow₀ (by linarith only [p5r S])

theorem apos (S : Std C0 Cde CE1 CE2 H X) : (0 : ℝ) < X.a := by
  have hne : (X.a : ℝ) ≠ 0 := by
    intro h
    have hp := S.pab
    rw [h, zero_div] at hp
    linarith only [hp, p5r S]
  exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hne)

theorem LaLeK (S : Std C0 Cde CE1 CE2 H X) : X.La C0 ≤ X.k := by
  have hL := S.LaN
  have hN := S.N2
  have hLa := S.La1
  have h : 2 * X.La C0 ≤ X.N * X.La C0 := mul_le_mul_of_nonneg_right hN (zero_le_one.trans hLa)
  linarith only [h, hL, hLa]

theorem kYLab (S : Std C0 Cde CE1 CE2 H X) : X.k * X.Y * X.La C0 * X.b' ≤ X.a := by
  have hk0 : 0 ≤ X.k := by linarith only [k5 S]
  have hY := S.Y1
  have hLa := S.La1
  have hN := S.N2
  have hlog := S.loga
  have hYN : 1 ≤ X.Y * X.N := one_le_mul_of_one_le_of_one_le hY (by linarith only [hN])
  have hv : 1 * 1 ≤ X.Y * X.N * Real.log X.a := mul_le_mul hYN hlog zero_le_one (zero_le_one.trans hYN)
  have hu : 0 ≤ X.k * X.Y * X.La C0 :=
    mul_nonneg (mul_nonneg hk0 (zero_le_one.trans hY)) (zero_le_one.trans hLa)
  have h1 : X.k * X.Y * X.La C0 * (1 * 1) ≤ X.k * X.Y * X.La C0 * (X.Y * X.N * Real.log X.a) :=
    mul_le_mul_of_nonneg_left hv hu
  have h2 : X.k * X.Y * X.La C0 ≤ X.a / X.b' := by
    linarith only [h1, S.ab]
  rw [le_div_iff₀ S.bpos] at h2
  exact h2

theorem kb (S : Std C0 Cde CE1 CE2 H X) : X.k * X.b' ≤ X.a := by
  have h := kYLab S
  have hk0 : 0 ≤ X.k := by linarith only [k5 S]
  have hY := S.Y1
  have hLa := S.La1
  have hYL : 1 ≤ X.Y * X.La C0 := one_le_mul_of_one_le_of_one_le hY hLa
  have hkb : 0 ≤ X.k * X.b' := mul_nonneg hk0 S.bpos.le
  have h' : X.k * X.b' * 1 ≤ X.k * X.b' * (X.Y * X.La C0) := mul_le_mul_of_nonneg_left hYL hkb
  linarith only [h, h']

theorem ba (S : Std C0 Cde CE1 CE2 H X) : X.b' ≤ X.a := by
  have hk : (1 : ℝ) ≤ X.k := by linarith only [k5 S]
  simpa only [one_mul] using (mul_le_mul_of_nonneg_right hk S.bpos.le).trans (kb S)

theorem Hc2 (S : Std C0 Cde CE1 CE2 H X) (hH : 0 ≤ H) : H * (X.k ^ 3 * X.Q ^ 2 * X.c * X.Y) ≤ X.b' := by
  have hS := S.Hc
  have hQ := Q1 S
  have hN := S.N2
  have hk0 : 0 ≤ X.k := by linarith only [k5 S]
  have hY0 : 0 ≤ X.Y := zero_le_one.trans S.Y1
  have hQ2 : 1 ≤ X.Q ^ 2 := one_le_pow₀ hQ
  have hNQ : 1 ≤ X.N * X.Q ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith only [hN]) hQ2
  have hw : 0 ≤ H * X.k ^ 3 * X.Q ^ 2 * (X.c : ℝ) * X.Y :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hH (pow_nonneg hk0 3)) (sq_nonneg X.Q))
      (Nat.cast_nonneg _)) hY0
  have h' := mul_le_mul_of_nonneg_left hNQ hw
  linarith only [hS, h']

theorem Hb1 (S : Std C0 Cde CE1 CE2 H X) (hH : 0 ≤ H) : H * (X.k ^ 3 * X.Q * X.Y) ≤ X.b' := by
  have hS := S.Hb
  have hQ := Q1 S
  have hN := S.N2
  have hk0 : 0 ≤ X.k := by linarith only [k5 S]
  have hY0 : 0 ≤ X.Y := zero_le_one.trans S.Y1
  have hQ3 : 1 ≤ X.Q ^ 3 := one_le_pow₀ hQ
  have hNQ : 1 ≤ X.N * X.Q ^ 3 := one_le_mul_of_one_le_of_one_le (by linarith only [hN]) hQ3
  have hw : 0 ≤ H * X.k ^ 3 * X.Q * X.Y :=
    mul_nonneg (mul_nonneg (mul_nonneg hH (pow_nonneg hk0 3)) (zero_le_one.trans hQ)) hY0
  have h' := mul_le_mul_of_nonneg_left hNQ hw
  linarith only [hS, h']

end Std

end Formalism.MainNotions.ColumnSystems.Pf
