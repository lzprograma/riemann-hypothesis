module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SsetGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.NilpotentSubgroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnipotentRadicalContracting
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MulVecBvecApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Groups

@[expose] public section

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

lemma isClosed_N : IsClosed (Nset k r) := by
  apply GlobalTheory.ProdHaar.isClosed_Nset

lemma S_sub_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ Sset k r z) :
    g ∈ UH (Hpk k r) := by
  obtain ⟨h, hh, n, hn, rfl⟩ := hg
  exact mul_mem_UH hh.1 hn.1

lemma mem_S_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Sset k r z ↔ ∃ h ∈ UWset k r z, Hpk k r * hᴴ * Hpk k r * g ∈ Nset k r := by
  constructor
  · rintro ⟨h, hh, n, hn, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [← Matrix.mul_assoc, inv_mul_UH hh.1, Matrix.one_mul]; exact hn
  · rintro ⟨h, hh, hn⟩
    refine ⟨h, hh, _, hn, ?_⟩
    rw [← inv_eq_UH hh.1, ← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]

lemma isClosed_S (hK : IsCompact (UWset k r z)) : IsClosed (Sset k r z) := by
  apply _root_.ReciprocityTheory.ChartRestriction.DS.Lap.groups_sset_closed <;> assumption

lemma one_mem_S : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Sset k r z :=
  ⟨1, one_mem_UW, 1, (nilpotent_subgroup k r).1, (Matrix.one_mul 1).symm⟩

lemma mul_mem_S {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Sset k r z) (hb : b ∈ Sset k r z) : a * b ∈ Sset k r z := by
  obtain ⟨h1, hh1, n1, hn1, rfl⟩ := ha
  obtain ⟨h2, hh2, n2, hn2, rfl⟩ := hb
  refine ⟨h1 * h2, mul_mem_UW hh1 hh2, h2⁻¹ * n1 * h2 * n2,
    (nilpotent_subgroup k r).2.1 _ ?_ _ hn2, ?_⟩
  · simpa [inv_inv_UH hh2.1] using uw_conj_N (inv_mem_UW hh2) hn1
  · calc h1 * n1 * (h2 * n2) = h1 * (h2 * h2⁻¹) * n1 * h2 * n2 := by
          rw [mul_inv_UH hh2.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = h1 * h2 * (h2⁻¹ * n1 * h2 * n2) := by simp only [Matrix.mul_assoc]

lemma inv_mem_S {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Sset k r z) : a⁻¹ ∈ Sset k r z ∧ a * a⁻¹ = 1 := by
  refine ⟨?_, mul_inv_UH (S_sub_UH ha)⟩
  obtain ⟨h, hh, n, hn, rfl⟩ := ha
  refine ⟨h⁻¹, inv_mem_UW hh, h * n⁻¹ * h⁻¹,
    uw_conj_N hh ((nilpotent_subgroup k r).2.2 _ hn), ?_⟩
  rw [Matrix.mul_inv_rev]
  calc n⁻¹ * h⁻¹ = (h⁻¹ * h) * n⁻¹ * h⁻¹ := by rw [inv_mul_UH' hh.1, Matrix.one_mul]
    _ = h⁻¹ * (h * n⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]

theorem sGroup_of (hUW : UWCompact) : SsetGroup := by
  intro k r z hz hT
  exact ⟨isClosed_S (hUW k r z hz hT), one_mem_S, fun a ha b hb => mul_mem_S ha hb,
    fun a ha => inv_mem_S ha⟩

end PI.QuotSetU.UnitaryGroupMassFormula.SW
