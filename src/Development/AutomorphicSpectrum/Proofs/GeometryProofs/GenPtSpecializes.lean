module

import Development.AutomorphicSpectrum.Statements.GeometryStatements.EqOfSpecializes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptInh

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dom (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by
  exact Function.Injective.isDomain (genMap ξ p) (h.inj p)

theorem nogen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  apply GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag.eq_of_specializes <;> assumption

end GlobalTheory.CompanionTheory.Ar.CptInh
