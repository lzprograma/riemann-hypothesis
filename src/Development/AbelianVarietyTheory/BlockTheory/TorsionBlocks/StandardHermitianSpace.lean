module

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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice NumberField Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace

def intVecs (D : D7) (n : ℕ) : Set (Fin n → D.host.E) :=
  {x | ∀ a, x a ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)}

variable {D : D7}

theorem baseLat_eq {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (i : Fin D.R.m) :
    (L.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = L0c D (Vc D i) := by
  obtain ⟨c, hc⟩ := hL.βV i
  unfold Formalism.IndefR.Lev.IsBaseFrame at hc
  obtain ⟨-, -, -, h1, h2⟩ := hc
  ext x
  constructor
  · intro hx
    simpa using h2 x hx
  · intro hx
    simpa using h1 x hx

end GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace

end
