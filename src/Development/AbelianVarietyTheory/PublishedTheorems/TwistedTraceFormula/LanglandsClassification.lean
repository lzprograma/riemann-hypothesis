module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
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

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar)
open scoped InnerProductSpace Topology

namespace GlobalTheory.Published

namespace Langlands

def IsRightDeriv {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (X : Matrix (Fin n) (Fin n) ℂ) (f f' : UJ ε → V) : Prop :=
  ∀ g, HasDerivAt (fun t : ℝ => f (g * expG ε X t)) (f' g) 0

def Quotient : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν →
    (∀ f ∈ I.fns, IsKFinFun f → ∃ h ∈ I.oppFns, IsKFinFun h ∧ I.IsIntegral ν f h) ∧
    (∀ f ∈ I.fns, IsKFinFun f → ∀ X ∈ lieSet ε, ∀ f' h h', IsRightDeriv X f f' → I.IsIntegral ν f h →
      I.IsIntegral ν f' h' → IsRightDeriv X h h') ∧
    ∃ Z : Submodule ℂ I.H, (Z : Set I.H) = I.intKer ν ∧ IsGKSub ε I.ρ Z ∧ Z ≠ kFinVec ε I.ρ ∧
      (∀ Y, IsGKSub ε I.ρ Y → Y = kFinVec ε I.ρ ∨ Y ≤ Z) ∧
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π ∧ IsFactor ε I.ρ Z (kFinVec ε I.ρ) π

end Langlands


end GlobalTheory.Published

end
