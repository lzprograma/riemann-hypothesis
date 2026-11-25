module

public import Formalism.LocalToGlobal.ComplexLatticeArea
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterionSecond
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

export Formalism.ComplexLatticeArea
  (Bf Bf_swap Bf_sub_zsmul_left Bf_sub_zsmul_right cramer Bf_comb cast_toNat area_spec)

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

section Host

variable {R : Ranks} (H : Host R)

abbrev beH : ℂ := Complex.I * (Real.sqrt H.d : ℂ)
abbrev phH (c : 𝓞 H.K) : ℂ := H.φ₀ (((c : H.K) : H.E))
def OKcH (z : ℂ) : Prop := ∃ x y : ℤ, Even (x - y) ∧ z = ((x : ℂ) + (y : ℂ) * beH H) / 2

theorem d_pos_host : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
theorem sq_sqrtC_host : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (d_pos_host H).le]; simp
theorem be_sq_host : beH H ^ 2 = -(H.d : ℂ) := by rw [beH, mul_pow, Complex.I_sq, sq_sqrtC_host]; ring
theorem conj_be_host : starRingEnd ℂ (beH H) = -beH H := by simp [beH, Complex.conj_ofReal]
theorem d_mod_host : ∃ k : ℤ, (H.d : ℤ) = 4 * k + 3 := ⟨(H.d : ℤ) / 4, by have := H.hyp.2.2.2.1; omega⟩
theorem b_sq_host : H.sqd ^ 2 = -(H.d : H.E) :=
  H.φ₀.injective (by rw [map_pow, H.φ₀_mem, be_sq_host, map_neg, map_natCast])
theorem bK_mem_host : H.sqd ∈ H.K := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
def bK_host : H.K := ⟨H.sqd, bK_mem_host H⟩
theorem bK_sq_host : bK_host H ^ 2 = -(H.d : H.K) := Subtype.ext (by push_cast; exact b_sq_host H)

theorem okc_mul_host {z w : ℂ} (hz : OKcH H z) (hw : OKcH H w) : OKcH H (z * w) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  obtain ⟨x', y', ⟨a', ha'⟩, rfl⟩ := hw
  obtain ⟨k, hk⟩ := d_mod_host H
  obtain rfl : x = y + a + a := by omega
  obtain rfl : x' = y' + a' + a' := by omega
  refine ⟨-(2 * k + 1) * y * y' + a * y' + a' * y + 2 * a * a', y * y' + a * y' + a' * y,
    ⟨-(k + 1) * y * y' + a * a', by ring⟩, ?_⟩
  have hkC : (H.d : ℂ) = 4 * k + 3 := by exact_mod_cast hk
  have hsq := be_sq_host H
  push_cast
  linear_combination hsq * ((y : ℂ) * y' / 4) - hkC * ((y : ℂ) * y' / 4)

theorem okc_conj_host {z : ℂ} (hz : OKcH H z) : OKcH H (starRingEnd ℂ z) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  refine ⟨x, -y, ⟨a + y, by omega⟩, ?_⟩
  rw [map_div₀, map_add (f := _), map_mul, conj_be_host, map_intCast, map_intCast, map_ofNat]; push_cast; ring

theorem coord_eq_host (x y : ℤ) :
    ((x : ℂ) + (y : ℂ) * beH H) / 2 =
      (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt H.d / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

theorem im_coord_host (x y : ℤ) :
    (((x : ℂ) + (y : ℂ) * beH H) / 2).im = (y : ℝ) * Real.sqrt H.d / 2 := by
  rw [coord_eq_host]; simp

theorem half_int {F : Type*} [Field F] [CharZero F] (x : F) (k : ℤ)
    (hx : x ^ 2 = -(4 * (k : F) + 3)) : IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  push_cast; linear_combination hx / 4

def om_host : 𝓞 H.K :=
  ⟨(1 + bK_host H) / 2, half_int _ (d_mod_host H).choose (by
    have h2 : ((H.d : ℤ) : H.K) = ((4 * (d_mod_host H).choose + 3 : ℤ) : H.K) :=
      congrArg (fun t : ℤ => (t : H.K)) (d_mod_host H).choose_spec
    push_cast at h2; rw [bK_sq_host H]; linear_combination -h2)⟩

theorem ph_om_host : phH H (om_host H) = (1 + beH H) / 2 := by
  show H.φ₀ ((((1 + bK_host H) / 2 : H.K)) : H.E) = _
  have h2 : ((2 : H.K) : H.E) = 2 := by
    rw [show (2 : H.K) = 1 + 1 by norm_num, IntermediateField.coe_add, IntermediateField.coe_one]; norm_num
  push_cast; rw [h2, map_div₀, map_add (f := _), map_one, map_ofNat]
  exact congrArg (fun t => (1 + t) / 2) H.φ₀_mem

theorem Bf_lat_host (δ : ℂ) (c₁ c₂ : 𝓞 H.K) :
    Bf (δ * phH H c₁) (δ * phH H c₂) = Complex.normSq δ * (starRingEnd ℂ (phH H c₁) * phH H c₂).im := by
  have : starRingEnd ℂ (δ * phH H c₁) * (δ * phH H c₂) =
      (Complex.normSq δ : ℂ) * (starRingEnd ℂ (phH H c₁) * phH H c₂) := by
    rw [Complex.normSq_eq_conj_mul_self, map_mul]; ring
  rw [Bf, this]; simp [Complex.mul_im]

theorem div_okc_host (cc : Ideal (𝓞 H.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0)
    (L : AddSubgroup ℂ) (hL_mem : ∀ w ∈ L, ∃ c ∈ cc, w = δ * phH H c)
    (hL_sub : ∀ c ∈ cc, δ * phH H c ∈ L) (hokc_of : ∀ u : 𝓞 H.K, OKcH H (phH H u)) :
    ∃ m : ℕ, 0 < m ∧ area L = Complex.normSq δ * (Real.sqrt H.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKcH H (starRingEnd ℂ (phH H c') * phH H c / m) := by
  have hpair : ∀ c₁ c₂ : 𝓞 H.K, OKcH H (starRingEnd ℂ (phH H c₁) * phH H c₂) :=
    fun c₁ c₂ => okc_mul_host H (okc_conj_host H (hokc_of c₁)) (hokc_of c₂)
  have hn : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  have hs : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (d_pos_host H)
  have hκ : 0 < Complex.normSq δ * (Real.sqrt H.d / 2) := by positivity
  have hdisc : ∀ w₁ ∈ L, ∀ w₂ ∈ L, ∃ n : ℤ,
      Bf w₁ w₂ = Complex.normSq δ * (Real.sqrt H.d / 2) * n := by
    intro w₁ h₁ w₂ h₂
    obtain ⟨c₁, -, rfl⟩ := hL_mem w₁ h₁
    obtain ⟨c₂, -, rfl⟩ := hL_mem w₂ h₂
    obtain ⟨x, y, -, hz⟩ := hpair c₁ c₂
    exact ⟨y, by rw [Bf_lat_host, hz, im_coord_host]; ring⟩
  have hne : ∃ w₁ ∈ L, ∃ w₂ ∈ L, Bf w₁ w₂ ≠ 0 := by
    set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
    refine ⟨δ * phH H c, hL_sub c hc,
      δ * phH H (c * om_host H), hL_sub (c * om_host H) (cc.mul_mem_right _ hc), ?_⟩
    have hph : phH H (c * om_host H) = phH H c * ((1 + beH H) / 2) := by rw [← ph_om_host]; simp [phH]
    have hc1 : phH H c ≠ 0 := by
      simp only [phH, map_ne_zero_iff _ H.φ₀.injective]
      exact fun h => hc0 (RingOfIntegers.coe_eq_zero_iff.mp (Subtype.ext h))
    rw [Bf_lat_host, hph]
    have e : starRingEnd ℂ (phH H c) * (phH H c * ((1 + beH H) / 2)) =
        (Complex.normSq (phH H c) : ℂ) * ((1 + beH H) / 2) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    have e4 : (1 + beH H) / 2 =
        (((1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt H.d / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have e5 : ((Complex.normSq (phH H c) : ℂ) * ((((1 : ℝ) / 2 : ℝ) : ℂ) +
        ((Real.sqrt H.d / 2 : ℝ) : ℂ) * Complex.I)).im =
        Complex.normSq (phH H c) * (Real.sqrt H.d / 2) := by simp [Complex.mul_im]
    rw [e, e4, e5]
    exact mul_ne_zero hn.ne' (mul_ne_zero (Complex.normSq_pos.2 hc1).ne' (by positivity))
  obtain ⟨m, hm, harea, hall⟩ := area_spec L _ hκ hdisc hne
  refine ⟨m, hm, harea, fun c hc c' hc' => ?_⟩
  obtain ⟨x, y, -, hz⟩ := hpair c' c
  obtain ⟨n₁, h₁⟩ := hall _ (hL_sub c' hc') _ (hL_sub c hc)
  obtain ⟨n₂, h₂⟩ := hall _ (hL_sub c' hc') _ (hL_sub (c * om_host H) (cc.mul_mem_right _ hc))
  have hph : phH H (c * om_host H) = phH H c * ((1 + beH H) / 2) := by rw [← ph_om_host]; simp [phH]
  rw [Bf_lat_host, hz, im_coord_host, harea] at h₁
  rw [Bf_lat_host, hph, ← mul_assoc, hz, harea] at h₂
  have e2 : ((x : ℂ) + (y : ℂ) * beH H) / 2 * ((1 + beH H) / 2) =
      ((((x - H.d * y : ℤ) : ℂ) + ((x + y : ℤ) : ℂ) * beH H) / 2) / 2 := by
    push_cast; linear_combination (y : ℂ) / 4 * be_sq_host H
  rw [e2, Complex.div_ofNat_im, im_coord_host] at h₂
  have hy : (y : ℝ) = m * n₁ := by
    have := (mul_eq_zero.1 (show Complex.normSq δ * (Real.sqrt H.d / 2) * (y - m * n₁) = 0 by
      linear_combination h₁)).resolve_left hκ.ne'
    linarith
  have hxy : ((x + y : ℤ) : ℝ) = 2 * (m * n₂) := by
    have := (mul_eq_zero.1 (show Complex.normSq δ * (Real.sqrt H.d / 2) * (((x + y : ℤ) : ℝ) - 2 * (m * n₂)) = 0 by
      linear_combination 2 * h₂)).resolve_left hκ.ne'
    linarith
  have hyZ : y = m * n₁ := by exact_mod_cast hy
  have hxZ : x = 2 * m * n₂ - m * n₁ := by
    have : x + y = 2 * (m * n₂) := by exact_mod_cast hxy
    linarith
  refine ⟨2 * n₂ - n₁, n₁, ⟨n₂ - n₁, by ring⟩, ?_⟩
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hz, hxZ, hyZ]; field_simp; push_cast; ring

theorem good_of_okc_host {u : ℂ} (hu : OKcH H u) :
    ∃ a b : ℤ, Even (a - b) ∧
      2 * u / (Real.sqrt H.d : ℂ) = (((a : ℝ) / Real.sqrt H.d : ℝ) : ℂ) + (b : ℂ) * Complex.I := by
  obtain ⟨x, y, hxy, rfl⟩ := hu
  have hs : (Real.sqrt H.d : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (d_pos_host H)).ne'
  exact ⟨x, y, hxy, by push_cast; field_simp⟩

theorem ratio_eq_of_area_host {δ z w : ℂ} {A : ℝ} {m : ℕ} (h0 : δ ≠ 0) (hm : 0 < m)
    (harea : A = Complex.normSq δ * (Real.sqrt H.d / 2) * m) :
    (starRingEnd ℂ (δ * z) * (δ * w)) / (A : ℂ) =
      2 * (starRingEnd ℂ z * w / m) / (Real.sqrt H.d : ℂ) := by
  have hnz : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 h0).ne'
  have hs : (Real.sqrt H.d : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (d_pos_host H)).ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcd : starRingEnd ℂ δ ≠ 0 := by simpa using h0
  rw [harea]; simp only [map_mul]; push_cast
  rw [Complex.normSq_eq_conj_mul_self] at hnz ⊢; field_simp

end Host

variable (D : D7)

abbrev bb : D.host.E := D.host.sqd
abbrev be : ℂ := beH D.host
abbrev ph (c : 𝓞 D.host.K) : ℂ := phH D.host c
def OKc (z : ℂ) : Prop := OKcH D.host z
theorem d_pos : (0 : ℝ) < D.host.d := d_pos_host D.host
alias sqrt_pos := _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos
theorem d_mod : ∃ k : ℤ, (D.host.d : ℤ) = 4 * k + 3 := d_mod_host D.host
theorem phi_b : D.host.φ₀ (bb D) = be D := D.host.φ₀_mem
theorem b_sq : bb D ^ 2 = -(D.host.d : D.host.E) := b_sq_host D.host
def bK : D.host.K := bK_host D.host
theorem okc_of (u : 𝓞 D.host.K) : OKc D (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
  by apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of
theorem okc_mul {z w : ℂ} (hz : OKc D z) (hw : OKc D w) : OKc D (z * w) := okc_mul_host D.host hz hw
theorem coord_eq (x y : ℤ) : ((x : ℂ) + (y : ℂ) * be D) / 2 =
    (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := coord_eq_host D.host x y
theorem good_of_okc {u : ℂ} (hu : OKc D u) : Good D (2 * u / (Real.sqrt D.host.d : ℂ)) := good_of_okc_host D.host hu
theorem bK_sq : bK D ^ 2 = -(D.host.d : D.host.K) := bK_sq_host D.host
def om : 𝓞 D.host.K := om_host D.host
theorem ph_om : ph D (om D) = (1 + be D) / 2 := ph_om_host D.host
theorem div_okc (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area (lamOf D cc δ) = Complex.normSq δ * (Real.sqrt D.host.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKc D (starRingEnd ℂ (ph D c') * ph D c / m) :=
  div_okc_host D.host cc hcc δ hδ (lamOf D cc δ) (FL.lam_mem D cc δ)
    (fun c hc => AddSubgroup.subset_closure ⟨c, hc, rfl⟩) (okc_of D)

def HYYIntRec : Prop :=
  ∀ D : D7, ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
    ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L', IsIntegral ℤ (hYY D A B)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

theorem HfArithRec_of_int (h : HYYIntRec) : HfArithRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'
  obtain ⟨m, hm, harea, hdiv⟩ := div_okc D cc hcc.1 δ h0
  have hh : OKc D (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E)) :=
    okc_of D ⟨hYY D A B, h D N N' L L' hA A hA' B hB'⟩
  have hg := good_of_okc D (okc_mul D (hdiv c hc c' hc') hh)
  convert hg using 1
  have hr := ratio_eq_of_area_host D.host (z := ph D c') (w := ph D c) h0 hm harea
  calc _ = (starRingEnd ℂ (δ * ph D c') * (δ * ph D c)) / (area (lamOf D cc δ) : ℂ) *
            D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E) := by simp only [ph, phH]; ring
    _ = _ := by rw [hr]; ring

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
