module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

def NcGapGt (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h < |((x.1 - y.1 : ℚ) : ℝ)|

def NcGapGe (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |((x.1 - y.1 : ℚ) : ℝ)|

def minSig (S : SPar) : ℕ :=
  min (S.filter fun x => x.2 = true).card (S.filter fun x => x.2 = false).card

def shiftPar (c : ℚ) (S : SPar) : SPar := S.image fun x => (x.1 + c, x.2)

variable (D : D7)

def alV (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i - 1 / 2 else -(D.hc τ).e i

def alW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i else -(D.hc τ).e i - 1 / 2

def lamS (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alW D i τ) (parA (Ptw D) i τ)

def lamT (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alV D i τ) (parA (Ptw D) ((i : ℕ) + 1) τ)

def StepGap (i : Fin D.R.m) : Prop :=
  ∀ τ, NcGapGt (lamS D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGt (lamT D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGe (lamS D i τ) (120 * (D.R.rankY i : ℝ) * (minSig (lamS D i τ) : ℝ) ^ ((3 : ℝ) / 2))

end GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

end
