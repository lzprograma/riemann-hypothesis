module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

def Sg (l h w S η : ℕ) : ℝ :=
  (h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l + Real.logb l (2 * (h : ℝ)) + 1

def cW (l H : ℕ) : ℕ := ⌈1 + Real.logb l ((H : ℝ) + 1)⌉₊

private structure RecipSetup (l : ℕ) where
  x : ℝ
  y : ℝ
  z : ℝ
  hx : x = (l : ℝ)⁻¹
  hy : y = ((l : ℝ) - 1)⁻¹
  hz : z = ((l : ℝ) - 2)⁻¹
  eLy : (l : ℝ) * y = 1 + y
  eLz : ((l : ℝ) - 2) * z = 1
  px : 0 < x
  py : 0 < y
  pz : 0 < z
  hx1 : x ≤ 1 / 11
  hy1 : y ≤ 1 / 10
  iy : y = x + x * y
  hx2 : x ^ 2 ≤ x / 11
  hxy : x * y ≤ 11 / 10 * x ^ 2
  hP0 : 0 ≤ y + y ^ 2
  hP1 : y + y ^ 2 ≤ 121 / 100 * x
  hP2 : y + y ^ 2 ≤ 11 / 100
  hzP1 : z * (y + y ^ 2) ≤ 3 / 2 * x ^ 2
  hzP2 : z * (y + y ^ 2) ≤ 11 / 900
  hy2 : y ^ 2 ≤ 121 / 100 * x ^ 2
  hy2' : y ^ 2 ≤ 1 / 100
  hy2z : y ^ 2 * z ≤ 121 / 900 * x ^ 2
  hy2z' : y ^ 2 * z ≤ 1 / 900
  hzy : z * y ≤ 121 / 90 * x ^ 2
  hzy' : z * y ≤ 1 / 90

private def RecipSetup.of_le {l : ℕ} (hl : 11 ≤ l) : RecipSetup l :=
  let L : ℝ := l
  have hL : (11 : ℝ) ≤ L := by dsimp [L]; exact_mod_cast hl
  let x : ℝ := L⁻¹
  let y : ℝ := (L - 1)⁻¹
  let z : ℝ := (L - 2)⁻¹
  have h0 : 0 < L := by linarith
  have h1 : 0 < L - 1 := by linarith
  have h2 : 0 < L - 2 := by linarith
  have eLx : L * x = 1 := mul_inv_cancel₀ h0.ne'
  have e1 : (L - 1) * y = 1 := mul_inv_cancel₀ h1.ne'
  have eLy : L * y = 1 + y := by linear_combination e1
  have eLz : (L - 2) * z = 1 := mul_inv_cancel₀ h2.ne'
  have px : 0 < x := inv_pos.mpr h0
  have py : 0 < y := inv_pos.mpr h1
  have pz : 0 < z := inv_pos.mpr h2
  have hx1 : x ≤ 1 / 11 := by nlinarith only [hL, eLx, px]
  have hy1 : y ≤ 1 / 10 := by nlinarith only [hL, e1, py]
  have hz1 : z ≤ 1 / 9 := by nlinarith only [hL, eLz, pz]
  have iy : y = x + x * y := by linear_combination (-y) * eLx + x * e1
  have hyx : y ≤ 11 / 10 * x := by nlinarith only [hy1, iy, px]
  have hzx : z ≤ 11 / 9 * x := by
    have iz : z = x + 2 * (x * z) := by linear_combination (-z) * eLx + x * eLz
    nlinarith only [hz1, iz, px]
  have hx2 : x ^ 2 ≤ x / 11 := by nlinarith only [hx1, px]
  have hxy : x * y ≤ 11 / 10 * x ^ 2 := by nlinarith only [hyx, px]
  have hP0 : 0 ≤ y + y ^ 2 := by positivity
  have hP1 : y + y ^ 2 ≤ 121 / 100 * x := by nlinarith only [hy1, hyx, py]
  have hP2 : y + y ^ 2 ≤ 11 / 100 := by nlinarith only [hy1, py]
  have hzP1 : z * (y + y ^ 2) ≤ 3 / 2 * x ^ 2 := by nlinarith only [hzx, hP1, hP0, px]
  have hzP2 : z * (y + y ^ 2) ≤ 11 / 900 := by nlinarith only [hz1, hP2, hP0]
  have hy2 : y ^ 2 ≤ 121 / 100 * x ^ 2 := by nlinarith only [hyx, py, px]
  have hy2' : y ^ 2 ≤ 1 / 100 := by nlinarith only [hy1, py]
  have hy2z : y ^ 2 * z ≤ 121 / 900 * x ^ 2 := by nlinarith only [hy2, hz1, pz, px]
  have hy2z' : y ^ 2 * z ≤ 1 / 900 := by nlinarith only [hy2', hz1, pz]
  have hzy : z * y ≤ 121 / 90 * x ^ 2 := by nlinarith only [hzx, hyx, py, px]
  have hzy' : z * y ≤ 1 / 90 := by nlinarith only [hz1, hy1, py]
  { x, y, z, hx := rfl, hy := rfl, hz := rfl,
    eLy, eLz, px, py, pz, hx1, hy1, iy,
    hx2, hxy, hP0, hP1, hP2, hzP1, hzP2, hy2, hy2', hy2z, hy2z', hzy, hzy' }

private theorem RecipSetup.div_l {l : ℕ} (R : RecipSetup l) (a : ℝ) : a / l = a * R.x := by
  rw [R.hx, div_eq_mul_inv]

private theorem RecipSetup.div_l_sq {l : ℕ} (R : RecipSetup l) (a : ℝ) :
    a / (l : ℝ) ^ 2 = a * R.x ^ 2 := by
  rw [R.hx, inv_pow, div_eq_mul_inv]

private theorem RecipSetup.div_sub_one {l : ℕ} (R : RecipSetup l) (a : ℝ) :
    a / ((l : ℝ) - 1) = a * R.y := by
  rw [R.hy, div_eq_mul_inv]

private theorem RecipSetup.div_sub_two {l : ℕ} (R : RecipSetup l) (a : ℝ) :
    a / ((l : ℝ) - 2) = a * R.z := by
  rw [R.hz, div_eq_mul_inv]

private theorem RecipSetup.div_sub_one_two {l : ℕ} (R : RecipSetup l) (a : ℝ) :
    a / (((l : ℝ) - 1) * ((l : ℝ) - 2)) = a * (R.y * R.z) := by
  rw [R.hy, R.hz, div_eq_mul_inv, mul_inv]

private theorem RecipSetup.mul_l_div_sub_one_sq {l : ℕ} (R : RecipSetup l) (v : ℝ) :
    v * l / ((l : ℝ) - 1) ^ 2 = v * (R.y + R.y ^ 2) := by
  have key : (l : ℝ) * R.y ^ 2 = R.y + R.y ^ 2 := by linear_combination R.y * R.eLy
  rw [← key, R.hy, inv_pow]
  ring

private theorem RecipSetup.mul_x_nonneg {l : ℕ} (R : RecipSetup l) (n : ℕ) : 0 ≤ (n : ℝ) * R.x :=
  mul_nonneg (Nat.cast_nonneg _) R.px.le

private theorem RecipSetup.mul_x_sq_nonneg {l : ℕ} (R : RecipSetup l) (n : ℕ) :
    0 ≤ (n : ℝ) * R.x ^ 2 :=
  mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem tsum_three (l : ℕ) (hl : 11 ≤ l) (f : ℕ → ℝ) (x₀ x₁ X : ℝ) (hf : ∀ a, 0 ≤ f a)
    (h0 : f 0 ≤ x₀) (h1 : f 1 ≤ x₁) (h2 : ∀ a, 2 ≤ a → f a ≤ X) :
    ∑' a : ℕ, f a * ((l : ℝ) - 1) ^ (-(a : ℤ)) ≤
      x₀ + x₁ / ((l : ℝ) - 1) + X / (((l : ℝ) - 1) * ((l : ℝ) - 2)) := by
  have R := RecipSetup.of_le hl
  have hyl : R.y < 1 := by linarith [R.hy1]
  have hterm : ∀ a : ℕ, f a * ((l : ℝ) - 1) ^ (-(a : ℤ)) = f a * R.y ^ a := by
    intro a
    rw [zpow_neg, zpow_natCast, R.hy, inv_pow]
  have hpt : ∀ i : ℕ, f i * R.y ^ i ≤
      X * R.y ^ i + ((if i = 0 then x₀ - X else 0) + (if i = 1 then (x₁ - X) * R.y else 0)) := by
    rintro (_ | _ | i)
    · simp; linarith
    · simp; nlinarith [R.py]
    · simp
      exact mul_le_mul_of_nonneg_right (h2 _ (by lia)) (pow_nonneg R.py.le _)
  have H := ((hasSum_geometric_of_lt_one R.py.le hyl).mul_left X).add
    ((hasSum_ite_eq (0 : ℕ) (x₀ - X)).add (hasSum_ite_eq (1 : ℕ) ((x₁ - X) * R.y)))
  have hfs : Summable (fun i : ℕ => f i * R.y ^ i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hf i) (pow_nonneg R.py.le i)) hpt H.summable
  have hzy : R.z - R.y = R.y * R.z := by linear_combination (-R.z) * R.eLy + R.y * R.eLz
  have e1 : (1 - R.y)⁻¹ = 1 + R.z := inv_eq_of_mul_eq_one_right (by linear_combination hzy)
  calc ∑' a : ℕ, f a * ((l : ℝ) - 1) ^ (-(a : ℤ)) = ∑' a : ℕ, f a * R.y ^ a := tsum_congr hterm
    _ ≤ X * (1 - R.y)⁻¹ + ((x₀ - X) + (x₁ - X) * R.y) := hasSum_le hpt hfs.hasSum H
    _ = x₀ + x₁ / ((l : ℝ) - 1) + X / (((l : ℝ) - 1) * ((l : ℝ) - 2)) := by
      rw [e1, R.div_sub_one, R.div_sub_one_two]
      linear_combination X * hzy

theorem cW_le (l : ℕ) (hl : 11 ≤ l) (h η H : ℕ) (hη : η + 1 ≤ h) (hH : H ≤ h + η) :
    (cW l H : ℝ) ≤ 2 + Real.logb l (2 * (h : ℝ)) := by
  have hL : (1 : ℝ) < l := by exact_mod_cast (by lia : 1 < l)
  have hH1 : (H : ℝ) + 1 ≤ 2 * (h : ℝ) := by exact_mod_cast (by lia : H + 1 ≤ 2 * h)
  have hlog0 : 0 ≤ Real.logb l ((H : ℝ) + 1) :=
    Real.logb_nonneg hL (by exact_mod_cast Nat.succ_pos H)
  have hmono := Real.logb_le_logb_of_le hL (by positivity) hH1
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 + Real.logb l ((H : ℝ) + 1) by linarith)
  unfold cW
  linarith

private theorem logb_two_mul_natCast_nonneg_of_eleven_le (l n : ℕ) (hl : 11 ≤ l) :
    0 ≤ Real.logb l (2 * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.logb_nonneg (by exact_mod_cast (by lia : 1 < l))
      (by exact_mod_cast (by lia : 1 ≤ 2 * n))

theorem rr_le (l : ℕ) (hl : 11 ≤ l) (h w S η H H₁ : ℕ) (hη : η + 1 ≤ h)
    (hH : H ≤ h + η) (hH₁ : H₁ ≤ w + S + η) (s r : ℝ)
    (hs : s ≤ ((H₁ : ℝ) + cW l H + 3) + ((H : ℝ) + cW l H + 3) / ((l : ℝ) - 2))
    (hr : r ≤ s * l / ((l : ℝ) - 1) ^ 2 + cW l H) :
    r ≤ 2 * ((w : ℝ) + S + η) / l + 2 * (h : ℝ) / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * (h : ℝ)) + 3 ∧
    2 * ((w : ℝ) + S + η) / l + 2 * (h : ℝ) / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * (h : ℝ)) + 3 ≤
      3 * Sg l h w S η := by
  have R := RecipSetup.of_le hl
  have hc := cW_le l hl h η H hη hH
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  simp only [Sg, R.div_l, R.div_l_sq, R.div_sub_two, R.mul_l_div_sub_one_sq] at hs hr ⊢
  have hH1r : (H₁ : ℝ) ≤ (w : ℝ) + S + η := by exact_mod_cast hH₁
  have hHr : (H : ℝ) ≤ (h : ℝ) + η := by exact_mod_cast hH
  have hsP : s * (R.y + R.y ^ 2) ≤
      ((H₁ : ℝ) + cW l H + 3) * (R.y + R.y ^ 2) +
      ((H : ℝ) + cW l H + 3) * (R.z * (R.y + R.y ^ 2)) := by
    have := mul_le_mul_of_nonneg_right hs R.hP0
    linarith
  refine ⟨?_, ?_⟩
  · nlinarith [R.hP0, R.hP1, R.hP2, R.hzP1, R.hzP2, R.hx2, R.pz,
      R.mul_x_nonneg w, R.mul_x_nonneg S, R.mul_x_nonneg η, R.mul_x_sq_nonneg h]
  · linarith [R.mul_x_nonneg w, R.mul_x_nonneg S, R.mul_x_nonneg η, R.mul_x_sq_nonneg h]

theorem sig_le (l : ℕ) (hl : 11 ≤ l) (h w S η : ℕ) (h1 : 1 ≤ h) (hG : w + S ≤ h) :
    (⌈((2 * (w + S) : ℕ) + ((2 * h / (l - 1) + 1 : ℕ) : ℝ)) * l / ((l : ℝ) - 1) ^ 2 + 1⌉₊ : ℝ) ≤
      3 * Sg l h w S η := by
  have R := RecipSetup.of_le hl
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  have hm : ((2 * h / (l - 1) : ℕ) : ℝ) ≤ 2 * (h : ℝ) * R.y := by
    calc ((2 * h / (l - 1) : ℕ) : ℝ) ≤ ((2 * h : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ = 2 * (h : ℝ) * R.y := by
        rw [Nat.cast_sub (by lia), Nat.cast_one, R.hy, div_eq_mul_inv]
        push_cast; ring
  refine le_trans (Nat.ceil_lt_add_one (by positivity)).le ?_
  simp only [Sg, R.div_l, R.div_l_sq, R.mul_l_div_sub_one_sq]
  push_cast
  have b1 : (2 * ((w : ℝ) + S) + ((2 * h / (l - 1) : ℕ) : ℝ) + 1) * (R.y + R.y ^ 2) ≤
      (2 * ((w : ℝ) + S) + 2 * (h : ℝ) * R.y + 1) * (121 / 100 * R.x) := by
    have := R.hP0
    have := R.hP1
    have := R.py.le
    gcongr
  have b2 := mul_le_mul_of_nonneg_left R.hxy (Nat.cast_nonneg h)
  linarith [R.hx1, R.mul_x_nonneg w, R.mul_x_nonneg S, R.mul_x_nonneg η, R.mul_x_sq_nonneg h]

theorem Aa_cut_le (l : ℕ) (hl : 11 ≤ l) (h w S η H H₁ H₂ : ℕ) (hη : η + 1 ≤ h)
    (hH : H ≤ h + η) (hH₁ : H₁ ≤ h + η) (hH₂ : H₂ ≤ w + S + η) (s A : ℝ)
    (hs : s ≤ ((H₁ : ℝ) + cW l H + 3) + ((H₂ : ℝ) + cW l H + 3) / ((l : ℝ) - 1) +
      ((H : ℝ) + cW l H + 3) / (((l : ℝ) - 1) * ((l : ℝ) - 2)))
    (hA : A ≤ s / ((l : ℝ) - 1) + 1) :
    A ≤ (H₁ : ℝ) / l + 2 * Sg l h w S η := by
  have R := RecipSetup.of_le hl
  have hc := cW_le l hl h η H hη hH
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  simp only [Sg, R.div_l, R.div_l_sq, R.div_sub_one, R.div_sub_one_two] at hs hA ⊢
  have hH1r : (H₁ : ℝ) ≤ (h : ℝ) + η := by exact_mod_cast hH₁
  have hH2r : (H₂ : ℝ) ≤ (w : ℝ) + S + η := by exact_mod_cast hH₂
  have hHr : (H : ℝ) ≤ (h : ℝ) + η := by exact_mod_cast hH
  have hsy : s * R.y ≤ ((H₁ : ℝ) + cW l H + 3) * R.y +
      ((H₂ : ℝ) + cW l H + 3) * R.y ^ 2 + ((H : ℝ) + cW l H + 3) * (R.y ^ 2 * R.z) := by
    have := mul_le_mul_of_nonneg_right hs R.py.le
    linarith
  have d0 : (H₁ : ℝ) * R.y = (H₁ : ℝ) * R.x + (H₁ : ℝ) * (R.x * R.y) := by
    linear_combination (H₁ : ℝ) * R.iy
  nlinarith [R.hx2, R.hxy, R.hy1, R.hy2, R.hy2', R.hy2z, R.hy2z', R.px, R.py, R.pz,
    R.mul_x_nonneg w, R.mul_x_nonneg S, R.mul_x_nonneg η, R.mul_x_sq_nonneg h]

theorem Aa_le (l : ℕ) (hl : 11 ≤ l) (h w S η H H₁ : ℕ) (hη : η + 1 ≤ h)
    (hH : H ≤ h + η) (hH₁ : H₁ ≤ h + η) (s A : ℝ)
    (hs : s ≤ ((H₁ : ℝ) + cW l H + 3) + ((H : ℝ) + cW l H + 3) / ((l : ℝ) - 2))
    (hA : A ≤ s / ((l : ℝ) - 1) + 1) :
    A ≤ (H₁ : ℝ) / l + 5 / 2 * Sg l h w S η := by
  have R := RecipSetup.of_le hl
  have hc := cW_le l hl h η H hη hH
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  simp only [Sg, R.div_l, R.div_l_sq, R.div_sub_one, R.div_sub_two] at hs hA ⊢
  have hH1r : (H₁ : ℝ) ≤ (h : ℝ) + η := by exact_mod_cast hH₁
  have hHr : (H : ℝ) ≤ (h : ℝ) + η := by exact_mod_cast hH
  have hsy : s * R.y ≤ ((H₁ : ℝ) + cW l H + 3) * R.y + ((H : ℝ) + cW l H + 3) * (R.z * R.y) := by
    have := mul_le_mul_of_nonneg_right hs R.py.le
    linarith
  have d0 : (H₁ : ℝ) * R.y = (H₁ : ℝ) * R.x + (H₁ : ℝ) * (R.x * R.y) := by
    linear_combination (H₁ : ℝ) * R.iy
  nlinarith [R.hx2, R.hxy, R.hy1, R.hzy, R.hzy', R.px, R.py, R.pz,
    R.mul_x_nonneg w, R.mul_x_nonneg S, R.mul_x_nonneg η, R.mul_x_sq_nonneg h]

end Formalism.MainNotions.N.FrobeniusPowerSeries
