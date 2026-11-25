module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTwUHolds
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem ea_applyD_map {σ τ K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  apply _root_.GlobalTheory.TwU.LowGen.applyD_map <;> assumption

def ea_InClassA (X : Sys p) {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧ ∀ α : X.ZA j →₀ ℕ,
    MvPowerSeries.coeff α F = ∑ i ∈ range (α.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff α (h ^ i * g i))

def ea_RestSU (X : Sys p) (Y : Pend X) : Prop :=
  DworkLemma p → BeProp p Y.be → ∀ (v : X.Pl) (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc),
    IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K'] [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K')
      (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
      ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧
        ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))))

end Formalism.MainNotions.FormalGroupSystem.Pf
