module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ZpowNeOneOfClose
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut7.IwahoriTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut.SsTwist Polynomial UpperTheory.V UpperTheory.V.Af

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : Formalism.ConjugateSelfDual.IsPlaceOver A w}

theorem monodromy_vanishes_weilTwist_iff (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (x.lpTwist ξ hξ).mono0 ↔ x.mono0 := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff]
  rfl

theorem charPol_lpTwist_iff (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (y.lpTwist ξ hξ).charPol g ↔ x.charPol g = y.charPol g := by
  rw [charPol_lpTwist, charPol_lpTwist]
  exact ⟨scaleRoots_cancel (Units.ne_zero _), fun e => by rw [e]⟩

end GlobalTheory.GalCut7.IwahoriTwist

end
