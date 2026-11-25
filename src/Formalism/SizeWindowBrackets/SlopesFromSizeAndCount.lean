module

public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
public import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
public import Formalism.ThickAverageLoss.PartnersToFactorsAt
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
import Formalism.HarderNarasimhan.Statement
import Formalism.RankGapBounds.MeanBoundSecondForm
import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.SChain
import Formalism.SizeWindowBrackets.GaloisToProductIsIso

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SizeWindowBrackets.SBrDiv, Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

-- ===== clump member: Formalism.SizeWindowBrackets.SBrDiv =====
-- clump-header: {"m": "Formalism.SizeWindowBrackets.SBrDiv", "h": "module\n\npublic import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces\npublic import Mathlib.RingTheory.Ideal.Norm.AbsNorm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.HarderNarasimhan.Statement\nimport Formalism.RankGapBounds.MeanBoundSecondForm\nimport Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic\nimport Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse\nimport Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime\nimport Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith\nimport Formalism.ThickAverageLoss.PartnersToFactorsAt\n\n"}
section -- clump:auto
@[expose] public section

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

section Defs1
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

end Defs1

section Defs2
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}

end Defs2

section Defs3
variable {U0 : Type} {W : U0 → Type} [∀ u0, Fintype (W u0)] {Top : Type} {m f : ℕ}

end Defs3

section Defs4
variable {K : Type} [Field K] [NumberField K]

def lw (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)

def plOf (w : HeightOneSpectrum (𝓞 K)) : slopeLatticeData.FinPl K := ⟨w.asIdeal, w.isMaximal⟩

end Defs4

end Formalism.LFunctionChainParameters.LBrDiv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SizeWindowBrackets.SBrDiv =====

-- ===== clump member: Formalism.SizeWindowBrackets.SlopesFromSizeAndCount =====
-- clump-header: {"m": "Formalism.SizeWindowBrackets.SlopesFromSizeAndCount", "h": "module\n\npublic import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic\npublic import Formalism.SizeWindowBrackets.SBrDiv\npublic import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse\npublic import Formalism.HarderNarasimhan.StatementPl\npublic import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit\npublic import Formalism.ThickAverageLoss.PartnersToFactorsAt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime\nimport Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis\nimport Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith\nimport Formalism.SizeWindowBrackets.SChain\nimport Formalism.SizeWindowBrackets.GaloisToProductIsIso\n\n"}
section -- clump:auto
@[expose] public section

open Module NumberField Matrix IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBrDiv

structure Rows {I : Type} {m : ℕ} (F : Fam I m) where

  D : ℕ

  XE : InfinitePlace F.K → Matrix (Fin D) (Fin D) ℂ

  R : Submodule (𝓞 F.K) (Fin D → F.K)

  ψ : Module.Dual F.K (Fin D → F.K) →ₗ[F.K] F.Wd

namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)

end Fam6

namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)

end Fam6

section DefsB
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

end DefsB

section DefsB2
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsB2

structure FamC (I : Type) (m : ℕ) where

  K : Type
  [indexKFirst : Field K]
  [indexKSecond : NumberField K]
  [indexKThird : StarRing K]
  [indexKFourth : _root_.NumberField.IsTotallyComplex K]

  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]

  Dall : ℕ

  D : ℕ

  D1 : ℕ

  V : I → Type
  [indexVFirst : ∀ i, AddCommGroup (V i)]
  [indexVSecond : ∀ i, Module K (V i)]
  [indexVThird : ∀ i, Module (𝓞 K) (V i)]
  [indexVFourth : ∀ i, IsScalarTower (𝓞 K) K (V i)]

  r : I → ℕ

  Vf : I → Type
  [indexFFirst : ∀ i, AddCommGroup (Vf i)]
  [indexFSecond : ∀ i, Module K (Vf i)]
  [indexFThird : ∀ i, Module (𝓞 K) (Vf i)]
  [indexFFourth : ∀ i, IsScalarTower (𝓞 K) K (Vf i)]

  d : I → ℕ
  b' : Basis (Fin D) K Wd
  X' : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ

  cc : Submodule (𝓞 K) Wd
  b : ∀ i, Basis (Fin (r i)) K (V i)
  X : ∀ i, InfinitePlace K → Matrix (Fin (r i)) (Fin (r i)) ℂ

  M : ∀ i, Submodule (𝓞 K) (V i)

  N0 : ∀ i, Submodule (𝓞 K) (V i)
  bf : ∀ i, Basis (Fin (d i)) K (Vf i)
  Xf : ∀ i, InfinitePlace K → Matrix (Fin (d i)) (Fin (d i)) ℂ

  Mf : ∀ i, Submodule (𝓞 K) (Vf i)

  j : ∀ i, V i →ₗ[K] Vf i

  σ : I → slopeLatticeData.FinPl K →₀ ℤ

  τ : slopeLatticeData.FinPl K →₀ ℤ

  B : ∀ i, V i →ₗ[K] Wd

  v : InfinitePlace K

  Y : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℂ

  Y' : Matrix (Fin D) (Fin D) ℂ

  Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ

  Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ

  ga : I → ℝ

  c : I → ℂ

  Vrow : Matrix (Fin Dall) (Fin Dall) ℂ

  U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ

  J : Matrix (Fin Dall) (Fin D) ℂ

  J1 : Matrix (Fin Dall) (Fin D1) ℂ

  S : Finset (slopeLatticeData.FinPl K)
  gain : Fin m → slopeLatticeData.FinPl K → ℝ
  Fj : Fin m → slopeLatticeData.FinPl K → ℝ
  Ej : I → Fin m → slopeLatticeData.FinPl K → ℝ

  iop : ℕ → ℝ

  T : I → ℕ

  h : I → ℝ

  lam : I → ℝ
  Dstar : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

attribute [instance] FamC.indexKFirst FamC.indexKSecond FamC.indexKThird FamC.indexKFourth FamC.indexWFirst FamC.indexWSecond FamC.indexWThird FamC.indexWFourth
  FamC.indexVFirst FamC.indexVSecond FamC.indexVThird FamC.indexVFourth FamC.indexFFirst FamC.indexFSecond FamC.indexFThird FamC.indexFFourth

namespace FamC
variable {I : Type} {m : ℕ} (F : FamC I m)

end FamC

section DefsC
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsC

def E7 (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 7)))

namespace FamC
variable {I : Type} {m : ℕ} (F : FamC I m)

end FamC

section DefsD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsD

namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)

end Fam6

section DefsD'
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsD'

section Top6
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}

end Top6

end Formalism.LFunctionChainParameters.LChain6
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SizeWindowBrackets.SlopesFromSizeAndCount =====
