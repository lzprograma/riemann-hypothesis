module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Mathlib.Algebra.Order.Star.Int
import Formalism.HermitianLattices.StatementJac
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.TameVal

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := by
  apply GlobalTheory.GalToHecke.locK_eq_of_tame <;> assumption

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  apply GlobalTheory.GalToHecke.exists_approx <;> assumption

theorem locK_mem (χ : HChar L) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (htame : ∀ v, χ.TameAt v) (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 L)) (x : Lˣ) : χ.locK P x ∈ G := by
  classical
  have hpr : χ.ProductRule := GlobalTheory.Mem.Chr.CharModel.productRule (F := L) ⟨χ.1, χ.2⟩
  have key : ∀ (a : 𝓞 L) (ha : (a : L) ≠ 0), χ.locK P (Units.mk0 (a : L) ha) ∈ G := by
    intro a ha
    have ha' : a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1)
      (fun v => by split_ifs; exacts [ha', one_ne_zero])
    have hP := hy P (Finset.mem_insert_self _ _)
    simp only [ite_true] at hP
    have hy0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hP
      have hpos : 0 < P.valuation L (a : L) := zero_lt_iff.2 (by simpa using ha')
      have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
      rw [one_mul] at this
      exact absurd hP (not_le.2 this)
    have e1 : χ.locK P (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (a : L) ha) :=
      locK_eq_of_tame χ (htame P) _ _ hP
    have e2 : ∏ v ∈ insert P T, χ.locK v (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (y : L) hy0) := by
      refine Finset.prod_eq_single P (fun v hv hne => ?_) (fun h => absurd (Finset.mem_insert_self _ _) h)
      have h1 := hy v hv
      simp only [ite_eq_right hne] at h1
      rw [locK_eq_of_tame χ (htame v) 1 _ (by simpa using h1), map_one]
    have h := hpr (insert P T) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (Units.mk0 (y : L) hy0)
    rw [e2, e1] at h
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ insert P T),
        χ.val v ^ ordF v (Units.mk0 (y : L) hy0)) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 : _ ∈ G := h ▸ G.one_mem
    rw [G.mul_mem_cancel_right hF, G.mul_mem_cancel_left (hinf _)] at h1
    exact h1
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 L) (x : L)
  have hb0 : (b : L) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  have ha0 : (a : L) ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hab]
    change (a : L) / _ = 0
    rw [h, zero_div]
  have hx : x = Units.mk0 (a : L) ha0 * (Units.mk0 (b : L) hb0)⁻¹ := by
    apply Units.ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0) (G.inv_mem (key b hb0))

def unitsIn (M : Subfield ℂ) : Subgroup ℂˣ where
  carrier := {u | (u : ℂ) ∈ M}
  one_mem' := M.one_mem
  mul_mem' := fun ha hb => M.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : ℂˣ) : ℂ) ∈ M
    rw [Units.val_inv_eq_inv_val]; exact M.inv_mem ha

theorem sq_div_norm {z : ℂ} (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
  have h1 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' z
  have h2 : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  rw [zpow_ofNat, div_pow, ← h1]
  field_simp

end GlobalTheory.TameVal
