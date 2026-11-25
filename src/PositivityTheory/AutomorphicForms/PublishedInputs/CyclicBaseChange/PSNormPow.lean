module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.CBC.SNormPow_holds : UpperTheory.CBC.SNormPow := by
  intro K M _ _ _ _ _ w
  exact ⟨_, GlobalTheory.DelEps.WeilRes.normV_eq_pow w⟩
