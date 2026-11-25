module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical

theorem _root_.GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  first | exact @GlobalTheory.PairInfTypes.infTypesAt
