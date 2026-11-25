module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve


open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  open Polynomial in
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

end GlobalTheory.FieldSize.RayExistCurve
