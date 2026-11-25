module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange

@[expose] public section



section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
structure EllipticHypothesis : Prop where
  e1 : GlobalTheory.TwSys.Cheb
  e2 : GlobalTheory.Published.PoitouTateTotallyComplex
  e3 : GlobalTheory.Published.CohDimTwo
  e4 : GlobalTheory.Published.TameLocal
  e5 : LocalFiniteness
  e6 : LocalTateDuality
  e7 : LocalEulerChar
  e8 : GlobalFiniteness
  e9 : GlobalEulerChar
  e10 : UnramifiedOrthogonality
  e11 : BlochKatoReduction.Gen.ArchimedeanSignatureMatching
  e12 : GreenbergWiles
  e13 : GlobalTheory.Published.RayCharacterArtin
  e14 : GlobalTheory.Published.ChebotarevDegreeOne
  e15 : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator
  e16 : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  e17 : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  e18 : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  e19 : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  e20 : GlobalTheory.HeckeSupSt.HeckeReadTie
  e21 : GlobalTheory.Published.AutomorphicFormsFiniteGL
  e22 : _root_.UpperTheory.GalS.CuspUAlt
  e23 : GlobalTheory.Published.DeRhamPotSemistable
  e24 : _root_.UpperTheory.GalS.CarUAlt
  e25 : ∀ D : D7, LocalSituation.Conclusion5 D
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
def MultiplicityCondition {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Prop :=
  GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat
end
end GlobalTheory.Mem.Top.Bl
end
end
