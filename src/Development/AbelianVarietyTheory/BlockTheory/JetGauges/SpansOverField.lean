module

public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

section PhiC

variable (E : Type) [Field E] [NumberField E] [IsCMField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a

def outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) : 𝓞 E :=
  ∑ i, η (x i) * bar E (η' (x' i))

def IsPosHerm (l : Module.Dual (𝓞 E) X → Module.Dual (𝓞 E) X → 𝓞 E) : Prop :=
  (∀ η η', l η' η = bar E (l η η')) ∧
    ∀ η, η ≠ 0 → ∀ τ : E →+* ℂ, 0 < (τ (l η η : E)).re

def pairing (B : X → X → ℝ) {n : ℕ} (x x' : Fin n → X) : ℝ := (∑ i, B (x i) (x' i)) / 2

def phiC (B : X → X → ℝ) : EReal :=
  sInf {t : EReal | ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧ t = (pairing B x x' : ℝ)}

end PhiC

end GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
