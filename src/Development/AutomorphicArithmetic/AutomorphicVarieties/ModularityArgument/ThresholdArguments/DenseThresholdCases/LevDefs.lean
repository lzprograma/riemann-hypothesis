module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBaseChange

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc UpperTheory.V.Br
namespace UpperTheory.V.Lev
def FixedDvdAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n M : ℕ), 1 ≤ M →
    ∀ (w : HeightOneSpectrum (𝓞 F)), (M : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (k := w.adicCompletion F) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      (∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
        (rc (algNorm σ)).charPol (ineIncl h s) = (X - 1) ^ n) → HasFixed σ.ρ (KLoc F w n M)
def FixedUnrAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (μ : Fin n → ↥(Weil h) →* ℂˣ), (∀ s, (rc (algNorm σ)).charPol s = ∏ i, (X - C (μ i s : ℂ))) →
    (∀ i (s : ↥(Ine (F := F) A)), μ i (ineIncl h s) = 1) →
    GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ ∧
      ((∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) → GlobalTheory.SmGL.IsSpherical σ.ρ)
def FixedSsAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∀ (rc : IrrGL (k := w.adicCompletion F) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      (IsAbPol n (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) →
        ∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol s = (rc (algNorm σ)).charPol s) →
      (l ∣ M ∨ (∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨
        (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ → GlobalTheory.SmGL.IsSpherical σ.ρ)) →
      HasFixed σ.ρ (KLoc F w n M)
end UpperTheory.V.Lev
end
end
