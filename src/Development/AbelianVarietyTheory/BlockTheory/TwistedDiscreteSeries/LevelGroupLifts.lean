module

public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct

variable {D : D7}

def idealLatHat (V : HSp D) (I : Ideal (𝓞 D.host.E)) :
    AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ b ∈ I, ∃ z ∈ latGHat V 1, w = halfVec V b z}

def IsLift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (g : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) (k : GA D V) : Prop :=
  k ∈ GfC V ∧ gLat V k = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
    ∀ a b : Dw.La, (Submodule.Quotient.mk b : LaMod Dw l) = g (Submodule.Quotient.mk a) →
      (finHom V k).1.mulVec (finVec V (ι a)) - finVec V (ι b) ∈ idealLatHat V l.Mb

abbrev LevGrp (T : CoreJ D) (j : ℕ) : Type :=
  LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def iotaAt (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (hr : (T.V j σ).rank = D.R.r) :
    (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (T.V j σ).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

attribute [local instance 2000] Submodule.module

end GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
