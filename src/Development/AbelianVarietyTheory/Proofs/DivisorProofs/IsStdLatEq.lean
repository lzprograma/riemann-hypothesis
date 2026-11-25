module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

noncomputable section

namespace GlobalTheory.BotFrames

variable {D : D7} {T : Type} {A A' WW : HSp D}

def reRig (Y : Tri T A A' WW) (rA : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A) (rA' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW)
    (f : T → WO A WW → ℂ) (f' : T → WO A' WW → ℂ) : Tri T A A' WW :=
  { Y with rA := rA, rA' := rA', rW := rW, f := f, f' := f' }

abbrev botAlpha (L : LevCh D T) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)

abbrev botBeta {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m) : (AE D)ˣ →* Circle :=
  G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)

theorem isStd_lat_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.Λ = r'.Λ := by
  ext y
  rw [h.2.1, h'.2.1]

theorem isStd_s_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.s = r'.s :=
  funext fun τ => (h.2.2 τ).1.trans (h'.2.2 τ).1.symm

theorem isStd_B_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.B = r'.B :=
  funext fun τ => (h.2.2 τ).2.trans (h'.2.2 τ).2.symm

end GlobalTheory.BotFrames

end
