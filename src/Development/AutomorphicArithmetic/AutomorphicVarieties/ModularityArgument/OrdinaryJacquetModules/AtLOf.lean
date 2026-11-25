module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)

namespace UpperTheory.V.Z.Ord

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w)

def AtLT (r : Dec (F := L) A →* GL (Fin n) (Qbar l)) (lam : Wt L l n) (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) : Prop :=
  ∀ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) →
    (∀ i j, i ≠ j → ∃ y : Uo (w.adicCompletion L), ω i y ≠ ω j y) → Nonempty (σ.ρ.Equiv (PS ω)) →
  ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc → Lev.AbW (rc (algNorm σ)) →
    DRat ι h r (fun τ => Finset.univ.val.map fun j => htW lam j τ) fun s => (rc (algNorm σ)).charPol s

def AtLOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w) (r : G L Ω →* GL (Fin n) (Qbar l)) (HT : (L →+* Qbar l) → Multiset ℤ)
    (τ : SmIrr (GLw n w)) (lam : Wt L l n), (GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred) → Win.HasHTAt r HT w) →
    Win.LocGlobT ι r w τ → (∀ j : W.Emb l w, (HT (j.1.comp (algebraMap L _))).map (fun k : ℤ => (k : ℂ)) =
      (infOfWeight (lam (j.1.comp (algebraMap L _))).dual).map fun z => ((n : ℂ) - 1) / 2 - z) →
    AtLT ι h (r.comp (Dec (F := L) A).subtype) lam τ

end UpperTheory.V.Z.Ord

end
