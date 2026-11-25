module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicHaar

theorem exists_haar_rightInvariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ μ : Measure (GA E a), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a => ⟨Measure.haar, inferInstance, GlobalTheory.CovolGL.isMulRightInvariant E a Measure.haar⟩

end GlobalTheory.CompanionTheory.AdelicHaar
