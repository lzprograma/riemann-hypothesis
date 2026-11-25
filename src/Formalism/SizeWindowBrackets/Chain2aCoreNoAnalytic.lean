module

public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Formalism.HarderNarasimhan.Statement
import Formalism.RankGapBounds.MeanBoundSecondForm
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.SChain
import Formalism.ThickAverageLoss.PartnersToFactorsAt

@[expose] public section

open Module NumberField Matrix
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

instance decFinPl (K : Type) [Field K] [NumberField K] : DecidableEq (slopeLatticeData.FinPl K) := Classical.decEq _

section Places
variable {K : Type} [Field K] [NumberField K]

def ramE (w : slopeLatticeData.FinPl K) : ℝ := (w.1.ramificationIdx ℤ : ℝ)

end Places

structure Fam (I : Type) (m : ℕ) where

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

  κ : Type
  [firstRealIndex : Fintype κ]
  [secondRealIndex : DecidableEq κ]

  κ₁ : Type
  [firstRationalIndex : Fintype κ₁]
  [secondRationalIndex : DecidableEq κ₁]

  V : I → Type
  [indexVFirst : ∀ i, AddCommGroup (V i)]
  [indexVSecond : ∀ i, Module K (V i)]
  [indexVThird : ∀ i, Module (𝓞 K) (V i)]
  [indexVFourth : ∀ i, IsScalarTower (𝓞 K) K (V i)]

  ι : I → Type
  [indexCFirst : ∀ i, Fintype (ι i)]
  [indexCSecond : ∀ i, DecidableEq (ι i)]

  Vf : I → Type
  [indexFFirst : ∀ i, AddCommGroup (Vf i)]
  [indexFSecond : ∀ i, Module K (Vf i)]
  [indexFThird : ∀ i, Module (𝓞 K) (Vf i)]
  [indexFFourth : ∀ i, IsScalarTower (𝓞 K) K (Vf i)]

  ιf : I → Type
  [indexDFirst : ∀ i, Fintype (ιf i)]
  [indexDSecond : ∀ i, DecidableEq (ιf i)]
  b' : Basis κ K Wd
  X' : InfinitePlace K → Matrix κ κ ℂ

  cc : Submodule (𝓞 K) Wd
  b : ∀ i, Basis (ι i) K (V i)
  X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ

  M : ∀ i, Submodule (𝓞 K) (V i)

  N0 : ∀ i, Submodule (𝓞 K) (V i)
  bf : ∀ i, Basis (ιf i) K (Vf i)
  Xf : ∀ i, InfinitePlace K → Matrix (ιf i) (ιf i) ℂ

  Mf : ∀ i, Submodule (𝓞 K) (Vf i)

  σ : I → slopeLatticeData.FinPl K →₀ ℤ

  τ : slopeLatticeData.FinPl K →₀ ℤ

  B : ∀ i, V i →ₗ[K] Wd

  v : InfinitePlace K
  Y : ∀ i, Matrix (ι i) (ι i) ℂ
  Y' : Matrix κ κ ℂ
  Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ
  γ : I → ℝ
  Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ
  Vr : ∀ i, Matrix (ιf i) (ι i) ℂ

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

attribute [instance] Fam.indexKFirst Fam.indexKSecond Fam.indexKThird Fam.indexKFourth Fam.indexWFirst Fam.indexWSecond Fam.indexWThird Fam.indexWFourth Fam.firstRealIndex Fam.secondRealIndex Fam.firstRationalIndex Fam.secondRationalIndex
  Fam.indexVFirst Fam.indexVSecond Fam.indexVThird Fam.indexVFourth Fam.indexCFirst Fam.indexCSecond Fam.indexFFirst Fam.indexFSecond Fam.indexFThird Fam.indexFFourth Fam.indexDFirst Fam.indexDSecond

namespace Fam

variable {I : Type} {m : ℕ} (F : Fam I m)

def N' (u : I) : Submodule (𝓞 F.K) (F.V u) := slopeLatticeData.modLat (F.σ u) (F.N0 u)

def du (u : I) : ℝ := (Fintype.card (F.ι u) : ℝ)

end Fam

structure Glob where

  x : ℝ

  ε : ℝ

  k : ℝ

  La : ℝ

  v : ℝ

  lg : ℝ

  delBar : ℝ

  etaBar : ℝ

  eBar : ℝ

end Formalism.LFunctionChainParameters.LChain2
