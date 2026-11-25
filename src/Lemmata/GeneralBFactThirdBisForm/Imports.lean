module

public import Mathlib.MeasureTheory.Constructions.Pi
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBounds

@[expose] public section

namespace Bl.general_b_fact_third_bis_form

theorem goal1 :
  ∀ {ι P β : Type} [inst : Fintype.{0} ι] [inst_1 : Fintype.{0} P] [inst_2 : MeasurableSpace.{0} β]
  (μ0 : MeasureTheory.Measure.{0} β) [MeasureTheory.SigmaFinite.{0} μ0],
  MeasureTheory.MeasurePreserving.{0, 0} (fun (x : ι → P → β) (p : P) (v : ι) ↦ x v p)
    (MeasureTheory.Measure.pi.{0, 0} fun (x : ι) ↦ MeasureTheory.Measure.pi.{0, 0} fun (x : P) ↦ μ0)
    (MeasureTheory.Measure.pi.{0, 0} fun (x : P) ↦ MeasureTheory.Measure.pi.{0, 0} fun (x : ι) ↦ μ0) :=
  @GlobalTheory.DegVol.RefCov.Transp.swap_mp

end Bl.general_b_fact_third_bis_form
