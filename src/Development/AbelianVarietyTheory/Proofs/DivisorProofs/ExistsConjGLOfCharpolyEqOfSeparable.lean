module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct

namespace GlobalTheory.SepConj

theorem conj_of_charpoly_eq_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K),
    a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := by
  intro K _ n a b he hs
  exact GlobalTheory.BCT.ClsFin.conj_of_charpoly a b hs he

end GlobalTheory.SepConj
