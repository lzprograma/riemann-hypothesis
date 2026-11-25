module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
namespace UpperTheory.V.Z.Desc.W
def TwAwayAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ)
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (R : G K Ω →* GL (Fin n) (Qbar l)), Continuous R →
    ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ) (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → Continuous μ →
    IsLAdicOf art ι κ m μ → ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal →
    ∀ τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K)), Good (IrrGL.of τ.ρ τ.smooth τ.irred) →
    Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc →
      IsWDOf ι R (rc (algNorm τ)) → IsWDOf ι (tw R μ) (rc (algNorm τ'))
def SphUntwAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (κ : HChar K)
    (w : HeightOneSpectrum (𝓞 K)) (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w τ'.ρ B →
    Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) → Good (IrrGL.of τ.ρ τ.smooth τ.irred) ∧
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc → Gd (rc (algNorm τ))
def PsFullAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (hh : Fin n → (L →+* Qbar l) → ℤ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ)
    (ph : Fin n → Ine (F := L) A →* (Qbar l)ˣ), IsSubquotient τ.ρ (Hi.PS ω) → (∀ i, Hi.OrdChar ι a (ω i) (hh i) (ψ i)) →
    (∀ j, V.W.IsWtPart h (ψ j) (fun e => hh j (e.1.comp (algebraMap L (w.adicCompletion L)))) (ph j)) → Function.Injective ph →
    Nonempty (τ.ρ.Equiv (Hi.PS ω))
end UpperTheory.V.Z.Desc.W
end
end
