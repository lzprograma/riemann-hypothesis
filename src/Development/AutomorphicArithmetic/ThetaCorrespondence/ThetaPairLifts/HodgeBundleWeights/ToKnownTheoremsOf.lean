module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth

@[expose] public section

section
namespace GlobalTheory.CovTop
structure PublishedHodgeBundleTheorems : Prop where
  p1 : GlobalTheory.Published.ToroidalCompactification
  p4 : GlobalTheory.Published.ArCalc
  p5 : GlobalTheory.Published.AbelianDeRham
  p8 : GlobalTheory.Published.RayClassFieldSt
  p16 : GlobalTheory.Published.GoodChernWeil
  p22 : GlobalTheory.Published.SemiAbelianHomExtension
  q1 : GlobalTheory.Published.GrothendieckMessing
  q4 : GlobalTheory.Published.PrismaticDieudonneHodge
  q6 : GlobalTheory.Published.KawamataViehweg
  q7 : GlobalTheory.Published.NefNumerics
  q9 : GlobalTheory.Published.ArithHilbertSamuel
  q11 : GlobalTheory.Published.CycleHeights
  q15 : GlobalTheory.Published.NadelVanishingAndNonKltDivisor
  q16 : GlobalTheory.Published.Principalisation
  q18 : GlobalTheory.Published.FormalAlgebraisation
theorem PublishedHodgeBundleTheorems.p18 (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : GlobalTheory.Published.FinitenessOfHermitianClasses := GlobalTheory.Published.finitenessOfHermitianClasses_holds
theorem PublishedHodgeBundleTheorems.toClassicalTheoremsOf (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hM : GlobalTheory.Published.GoodChernWeil → GlobalTheory.Published.MumfordProportionality) : _root_.GlobalTheory.CovTop.Hypotheses'' := by
  have hM' := hM h.p16
  refine ⟨h.p1, h.p4, h.p5, h.p8, ?_, h.p18, h.p22⟩
  first
    | exact hM'
end GlobalTheory.CovTop
end
