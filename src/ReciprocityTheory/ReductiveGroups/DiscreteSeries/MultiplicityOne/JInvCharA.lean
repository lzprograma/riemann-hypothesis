module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  apply ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec <;> assumption

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  apply ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec_mulVec <;> assumption

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at e
  exact e

theorem Hpk_sq : Hpk k r * Hpk k r = 1 := by
  exact mat_eq_of_mulVec' k r (fun v => by rw [← mulVec_mulVec, Hpk_mulVec_mulVec, one_mulVec])

end hpk

section wb
variable {k r : ℕ}

end wb

section cc
variable {k r : ℕ}

def isW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

section cc

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

def cc (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  embWb k r γ *ᵥ (fun i => conj (((embWb k r γ)⁻¹ *ᵥ v) i))

variable {γ}
variable (hE : IsUnit (embWb k r γ).det)
include hE

theorem gbar_mul (g g' : Mat k r) : gbar k r γ (g * g') = gbar k r γ g * gbar k r γ g' := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1 := nonsing_inv_mul _ hE
  have h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1 := mul_nonsing_inv _ hE
  have h1' : ∀ X : Mat k r, (embWb k r γ)⁻¹ * (embWb k r γ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2' : ∀ X : Mat k r, embWb k r γ * ((embWb k r γ)⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hB : (embWb k r γ)⁻¹ * (g * g') * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * g' * embWb k r γ) := by
    simp only [Matrix.mul_assoc, h2']
  rw [hB, Matrix.map_mul]
  simp only [Matrix.mul_assoc, h1']

theorem gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1 := nonsing_inv_mul _ hE
  have h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1 := mul_nonsing_inv _ hE
  have hm1 : (1 : Mat k r).map (starRingEnd ℂ) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp only [Matrix.mul_one, h1, hm1, h2]

theorem gbar_inv (A : Mat k r) (hA : IsUnit A.det) : gbar k r γ A⁻¹ = (gbar k r γ A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← gbar_mul hE, Matrix.mul_nonsing_inv _ hA, gbar_one hE]

end cc

end cc

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr
