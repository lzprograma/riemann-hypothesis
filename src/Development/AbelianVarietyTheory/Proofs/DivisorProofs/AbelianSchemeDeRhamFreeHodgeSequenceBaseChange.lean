module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations

@[expose] public section

namespace GlobalTheory

theorem abelianDeRham_free_hodge_baseChange : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧
      GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro hH
  obtain ⟨hF, hBC, -⟩ := GlobalTheory.abelianDeRham_free_baseChange_rigid hH
  exact ⟨hF, GlobalTheory.AbelianHodge.abelianDeRham_hodge
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH, hBC⟩

end GlobalTheory
