module

public import Formalism.QuotientMetricDivisors.PassageScaleFree
public import Formalism.QuotientMetricDivisors.Complement2Normaliser
public import Formalism.PairingDivisors.StatementX
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)

noncomputable section

namespace Formalism.AtG

def denIdeal {K : Type} [Field K] [NumberField K] (T : Finset (Pl K)) (a : Pl K → ℤ) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  ∏ w ∈ T, (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a w))

def rhoAt {K : Type} [Field K] (x y E : ℤ → K) (s : ℤ) : K :=
  if 1 ≤ s then y s / x s else E s * (y (1 - s) / x (1 - s))

def NormalisedPrimeUnitWeight : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ell : Pl K → ℕ),
    (∀ w, (ell w).Prime ∧ PlOver (ell w) w) →
    ∀ (S : Finset ℕ) (c : ℕ → ℝ), (∀ l ∈ S, l.Prime) → ∀ w : Pl K,
      wt S c w = (if ell w ∈ S then c (ell w) else 0) * (vw w (ell w : K) : ℝ)

def DisjointUnionFactorProduct : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (x : K) (dl : Pl K → ℝ)
    (Bδ : ℝ), x ≠ 0 → (∀ w, 0 ≤ dl w) → (∀ w, -(3 * dl w) ≤ (vw w x : ℝ)) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    HtLe (fun _ => 0) x (meanInf K (fun v => Real.posLog ‖v.embedding x‖) + 6 * Bδ)

def SlopeInequalityDenominators : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W) (T : Finset (Pl K))
      (a : Pl K → ℤ), A.FG → A ≠ ⊥ → B.FG → B ≠ ⊥ → Function.Injective φ →
      A.map (φ.restrictScalars (𝓞 K)) ≤
        Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) B →
      muMaxDef b X A ≤
        muMaxDef b' X' B + (htMap b X b' X' φ + 2 * ∑ w ∈ T, lw w * (a w : ℝ))

def FinitePlaceLiesOverPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ ell : Pl K → ℕ, ∀ w, (ell w).Prime ∧ PlOver (ell w) w

end Formalism.AtG
