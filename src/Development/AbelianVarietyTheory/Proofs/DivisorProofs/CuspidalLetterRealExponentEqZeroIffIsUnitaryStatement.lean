module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  first | exact @GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary
