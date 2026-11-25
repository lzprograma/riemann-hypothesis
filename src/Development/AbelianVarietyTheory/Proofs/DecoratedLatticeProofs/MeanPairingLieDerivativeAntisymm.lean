module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Mathlib.Dynamics.Ergodic.Action.Regular
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)

namespace GlobalTheory.RegSch.Ibp

variable {D : D7} {V : HSp D}

theorem isFiniteMeasure_autMeasure (m : Measure (GA D V)) [hm : m.IsHaarMeasure] :
    IsFiniteMeasure (autMeasure V m) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨by
    rw [autMeasure, quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd⟩

theorem isMulRightInvariant (m : Measure (GA D V)) [hm : m.IsHaarMeasure] : m.IsMulRightInvariant := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) m hfd (hfd.measure_ne_zero (NeZero.ne m))
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd).ne⟩

variable {θ : InfFam D} {τ : D.what₂.Tau}

end GlobalTheory.RegSch.Ibp
