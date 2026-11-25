module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

def perpSet (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ w ∈ W, Formalism.UG.hform s J w y = 0}

def IsSkew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ u u' : Fin n → A, Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') = 0

def InNil (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  IsSkew s J Y ∧ (∀ u, Y *ᵥ u ∈ perpSet s J W) ∧ (∀ u ∈ perpSet s J W, Y *ᵥ u ∈ W) ∧ ∀ u ∈ W, Y *ᵥ u = 0

def InCen (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  InNil s J W Y ∧ ∀ u ∈ perpSet s J W, Y *ᵥ u = 0

end Lie

variable (I : AutInst)

def spanAt (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (R : Set _))

def nilReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def cenReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def nilInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def cenInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def diagEmb (Y : Matrix (Fin I.n) (Fin I.n) I.E) : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
  fun v => Y.map (I.φ v)

def normAt (x : I.GA) (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) : ℝ :=
  Real.sqrt (∑ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Y v * I.P v * uMat (x.1 v)))

end GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets
