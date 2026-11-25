module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.T2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N

namespace SumRepresentations

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def StrongMultiplicityOneCuspidalSums : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

def IsobaricMultiplicityOne : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

end SumRepresentations

end Formalism.MainNotions.N.T2

namespace Formalism.MainNotions.N.T2

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations in
theorem litGoodO : Formalism.MainNotions.N.LitGoodO := by
  apply _root_.GlobalTheory.LitGood.litGoodO <;> assumption
end Formalism.MainNotions.N.T2
