module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic : ∀ D : D7, ∃ χ : IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (1 / 2)) ∧ ResEta D χ 1 ∧ UnramEverywhere D χ := by
  first | exact @GlobalTheory.Mem.EtaTilde.exists_etaTilde
