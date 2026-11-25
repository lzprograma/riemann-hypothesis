module

public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqDefiniteCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.DefiniteMeasure

open Formalism.IndefR.Lev GlobalTheory.Mem.VolExists

theorem exists_probHaar (P Q : ℕ) (h : P = 0 ∨ Q = 0) : ∃ ν : Measure (UpqT P Q), ν.IsHaarMeasure ∧
    ∀ m : Measure (UpqT P Q), (m.IsHaarMeasure ∧ IsProbabilityMeasure m) ↔ m = ν := by
  haveI : CompactSpace (UpqT P Q) := by
    rcases h with rfl | rfl
    exacts [(GlobalTheory.compactSpace_UpqT_definite Q).2, (GlobalTheory.compactSpace_UpqT_definite P).1]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let ν : Measure (UpqT P Q) := Measure.haarMeasure ⊤
  haveI hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure ⊤
  haveI hp : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
  refine ⟨ν, hν, fun m => ⟨fun ⟨h1, h2⟩ => ?_, fun e => e ▸ ⟨hν, hp⟩⟩⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure m ν

end GlobalTheory.Mem.DefiniteMeasure
