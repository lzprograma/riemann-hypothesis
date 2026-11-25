module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

def sumMat {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) : RealMat B :=
  fun τ => o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ)

def sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) : Lat B :=
  LW.map ((Matrix.mulVecLin o.iA).restrictScalars (𝓞 D.host.E)) ⊔
    LH.map ((Matrix.mulVecLin o.iB).restrictScalars (𝓞 D.host.E))

theorem sumMat_apply {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    sumMat o sW sH τ =
      o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ) := rfl

theorem mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) (y : Fin B.rank → D.host.E) :
    y ∈ sumLatO o LW LH ↔ ∃ x ∈ LW, ∃ x' ∈ LH, o.iA *ᵥ x + o.iB *ᵥ x' = y := by
  simp only [sumLatO, Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩
    exact ⟨x, hx, x', hx', rfl⟩
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
