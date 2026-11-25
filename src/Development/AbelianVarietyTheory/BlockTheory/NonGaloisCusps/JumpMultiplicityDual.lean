module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Core

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Ops

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def mulPeriod (b : BdR) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

def mapdR {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR :=
  AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)

end Ops

variable [TopologicalSpace G] (LL O : Type) [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL]

def CrysDeRhamCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → IsDR PD T.ρ

def StrictCore : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (f : T₀.V →ₗ[LL] T₁.V) (g : T₁.V →ₗ[LL] T₂.V),
    (∀ s x, f (T₀.ρ s x) = T₁.ρ s (f x)) → (∀ s x, g (T₁.ρ s x) = T₂.ρ s (g x)) →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsDR PD T₀.ρ → IsDR PD T₁.ρ → IsDR PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (∀ x ∈ FildR PD T₀.ρ τ a, mapdR (Qp := Qp) (BdR := BdR) f x = 0 → x = 0) ∧
      (FildR PD T₀.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) f) =
        FildR PD T₁.ρ τ a ⊓ LinearMap.ker (mapdR (Qp := Qp) (BdR := BdR) g) ∧
      (FildR PD T₁.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) g) = FildR PD T₂.ρ τ a

end Core

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def CrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → CrysDeRhamCore (P.PD K) ↥LL.1 ↥(OL LL)

def Strictness : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → StrictCore (P.PD K) ↥LL.1 ↥(OL LL)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual
