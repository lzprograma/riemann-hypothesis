module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.MulVecApplyOfRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCharA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN
import Mathlib.Tactic.Linter.Style
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Grp

variable {k r : ℕ}

theorem hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  apply ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr.Hpk_sq

theorem uh_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [conjTranspose_mul, mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem uh_inv {a : Mx k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hl : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc Hpk k r * aᴴ * Hpk k r * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', hpk_sq]
  have hinv : a⁻¹ = Hpk k r * aᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have h1 : a⁻¹ * a = 1 := by rw [hinv]; exact hl
  have h2 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hl)
  refine ⟨h2, h1, ?_⟩
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2]; simp

def lowS (k r a : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) where
  carrier := {y | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0}
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

theorem eI_val (a : Fin r) : (eI k r a).val = a.val := rfl

theorem maps_low {n : Mx k r} (hn : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      n i (eI k r a) = if i = eI k r a then 1 else 0) {a : ℕ} (har : a ≤ r) :
    ∀ y ∈ lowS k r a, n *ᵥ y ∈ lowS k r a := by
  intro y hy
  have hy' : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0 := hy
  show ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (n *ᵥ y) i = 0
  intro i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : a ≤ l.val
  · rw [hy' l hl, mul_zero]
  · have hlr : l.val < r := by omega
    have h1 := hn ⟨l.val, hlr⟩ i (by show (l : ℕ) ≤ i; omega)
    have heq : eI k r ⟨l.val, hlr⟩ = l := Fin.ext (eI_val _)
    rw [heq] at h1
    rw [h1, ite_eq_right (fun h => by subst h; omega), zero_mul]

theorem n_inv {n : Mx k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := by
  apply _root_.PI.AmpOrbQuot.nset_inv <;> assumption

theorem herm_inv {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ x) (h *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

theorem hpk_row_esI (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) l = if l = eI k r b then 1 else 0 := by
  have hb := b.isLt
  have hl := l.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem herm_esI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (esI k r b)) = y (eI k r b) := by
  have hs : star (bvec (esI k r b) : Fin (2 * r + k + 1) → ℂ) = bvec (esI k r b) := by
    ext l
    by_cases h : l = esI k r b <;> simp [bvec, h, Pi.star_apply]
  unfold herm
  rw [hs]
  simp [bvec, dotProduct, Matrix.mulVec, Pi.single_apply, hpk_row_esI]

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  unfold UWset at *
  simp only [Set.mem_setOf_eq] at hh ⊢
  obtain ⟨hU, hfix, hz⟩ := hh
  obtain ⟨-, h2, hinvU⟩ := uh_inv hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  exact ⟨hinvU, fun c => ⟨key _ (hfix c).1, key _ (hfix c).2⟩, key _ hz⟩

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ} {a b : Mx k r} (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) :
    a * b ∈ UWset k r z := by
  unfold UWset at *
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨haU, hafix, haz⟩ := ha
  obtain ⟨hbU, hbfix, hbz⟩ := hb
  refine ⟨uh_mul haU hbU, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hbfix c).1, (hafix c).1]
  · rw [← Matrix.mulVec_mulVec, (hbfix c).2, (hafix c).2]
  · rw [← Matrix.mulVec_mulVec, hbz, haz]

theorem n_on_Wb {n : Mx k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ lowS k r r := by
  unfold Nset at hn
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨-, -, hmid⟩ := hn
  have hu' : ∀ i : Fin (2 * r + k + 1), ↑i < r ∨ r + k < ↑i → u i = 0 := hu
  show ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n *ᵥ u - u) i = 0
  intro i hi
  rw [Pi.sub_apply, sub_eq_zero]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hm : i.val ≤ r + k
    · rw [hmid i i hi hm hi, ite_eq_left rfl, one_mul]
    · rw [hu' i (Or.inr (by omega)), mul_zero]
  · intro l _ hl
    by_cases hlm : r ≤ l.val ∧ l.val ≤ r + k
    · rw [hmid i l hlm.1 hlm.2 hi, ite_eq_right (fun h => hl h.symm), zero_mul]
    · rw [hu' l (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem conj_n {z : Fin (2 * r + k + 1) → ℂ} {h n : Mx k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) :
    h⁻¹ * n * h ∈ Nset k r := by
  apply _root_.WlocSk.UnitaryGroupBasics.uw_conj_mem <;> assumption

theorem grpAll : GrpAll := by
  intro k r z
  unfold GrpF
  refine ⟨fun a ha b hb => uh_mul ha hb, fun a ha => uh_inv ha, fun a ha => uw_inv ha,
    fun a ha => n_inv ha, fun h hh n hn => conj_n hh hn, fun h hh n hn => ?_,
    fun a ha b hb => uw_mul ha hb⟩
  have h1 := conj_n (uw_inv hh) hn
  have hU : h ∈ UH (Hpk k r) := by
    unfold UWset at hh
    exact hh.1
  obtain ⟨hinv1, -, -⟩ := uh_inv hU
  have hdet : IsUnit h.det := Matrix.isUnit_det_of_right_inverse hinv1
  rwa [Matrix.nonsing_inv_nonsing_inv h hdet] at h1

end Grp

end PI.WBL.Cv
