module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ := by
  first | exact @GlobalTheory.Ker.exists_test_of_fock
