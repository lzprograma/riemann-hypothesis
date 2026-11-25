module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def cjT (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) O :=
  fun a b => ⟨cj (Z b a), hO _ (Z b a).2⟩

def bRaw (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y y' : Fin (r + 1) → O) : E :=
  ∑ j, cj (y' j) * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j

def lamS (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y' : Fin (r + 1) → O) : E :=
  lamStarC cj (Z.map O.subtype) (fun b => (y' b : E))

def PairSet (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : Type :=
  {p : (MbMod Z₁ ≃ₗ[O] MbMod Z₂) × (MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂)) //
    (p.1 (bCls Z₁) = bCls Z₂ ∧ p.1 (eCl Z₁) = eCl Z₂) ∧
    (∀ y' y₂' : Fin (r + 1) → O, p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      lamS O cj Z₂ y₂' = lamS O cj Z₁ y') ∧
    (∀ y y' y₂ y₂' : Fin (r + 1) → O, p.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂ →
      p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      bRaw O cj Z₂ y₂ y₂' - bRaw O cj Z₁ y y' ∈ O)}

def projP (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (p : PairSet O cj hO Z₁ Z₂) : IsoMbe Z₁ Z₂ :=
  (⟨p.1.1, p.2.1⟩ : {γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂ // γ (bCls Z₁) = bCls Z₂ ∧ γ (eCl Z₁) = eCl Z₂})


def StepInj : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    Function.Injective (projP O cj hO Z₁ Z₂)


end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
