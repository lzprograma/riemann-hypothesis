module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
public import GroundTheory.AutomorphicForms.GL2.GJFEDefs
import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel


namespace UpperTheory.V.Z.Gam

def cntF {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ} {β : Fin n → ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W) : ℕ :=
  (Finset.univ.filter fun a : Set.range β => blockSize β a = 1 ∧ ∀ g ∈ integralGL F (blockSize β a),
    σ ((leviEquivPi F β).symm (Pi.mulSingle a g)) = 1).card

def LeviDiv : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (n : ℕ) (β : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W),
    IsAdmissible σ → σ.IsIrreducible → IsCuspidal σ → ∀ (κ : levi F n β →* ℝ≥0), Continuous κ →
    ∀ (μ : Measure (levi F n β)) [μ.IsHaarMeasure] (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 → ∀ γ : RatFunc ℂ,
    LeviFE F σ κ μ ψ γ → ∃ (P : ℂ[X]) (c : ℂ) (j : ℤ), P.eval 0 = 1 ∧ P.natDegree = cntF σ ∧ c ≠ 0 ∧
      γ = RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
        algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) * X))

def CoefInd : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (n : ℕ) [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V), IsSmooth π → ∀ (β : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi F n β) W), IsSmooth σ → ∀ ι : Representation.IntertwiningMap π (parabolicInd F n β σ),
    Function.Injective ι → ∀ (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ γ : RatFunc ℂ, InducedFE F σ μ ψ γ → IsGammaFactor F π μ ψ γ

def SuppBridge : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V) (s : Multiset (GlobalTheory.LocGL.IrrGL (k := F))),
    GlobalTheory.LocGL.HasSupport π s → ∀ (β : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi F n β) W), IsAdmissible σ → σ.IsIrreducible → IsCuspidal σ →
    ∀ ι : Representation.IntertwiningMap π (parabolicInd F n β σ), Function.Injective ι → cnt s 1 = cntF σ

def GamLocOf : Prop := LeviDiv → CoefInd → SuppBridge → GamLoc

end UpperTheory.V.Z.Gam
