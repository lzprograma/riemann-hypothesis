module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FixedVectorVanishing.FixedEqZeroOfMemISup

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

namespace SplitSph

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isIrreducible_comp_surj {H : Type} [Group H] (σ : Representation ℂ H W) (p : G →* H)
    (hp : Function.Surjective p) (hσ : σ.IsIrreducible) : Representation.IsIrreducible (σ.comp p) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσ
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hp g
  exact hY x v hv

end Abstract

end SplitSph

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

alias split_spherical := _root_.PositivityTheory.Rg.BcB.Loc.split_spherical2

end GlobalTheory.PfBCI

end
