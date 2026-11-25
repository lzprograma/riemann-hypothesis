module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

namespace UpperTheory.V.Z.Win.Birth

def ULoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (c : ℕ) (lam : ℂ) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), c ≠ 0 → lam ≠ 0 →
    HasU w σ.ρ c lam → ∃ ψ : Fin 2 → (w.adicCompletion F)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient σ.ρ (prinSeries ψ) ∧
      (∀ x, IsUnitAt w x → ψ 0 x = 1) ∧ lam ^ 2 = (normV w : ℂ) * (ψ 0 (atFin w (unif w)) : ℂˣ) ^ 2

def PsCent : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (ψ : Fin 2 → (w.adicCompletion F)ˣ →* ℂˣ),
    IsSubquotient σ.ρ (prinSeries ψ) → ∀ z v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((ψ 0 z * ψ 1 z : ℂˣ) : ℂ) • v

def PsPlain : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (ψ : Fin 2 → (w.adicCompletion F)ˣ →* ℂˣ),
    (∀ i, IsSmoothChar (ψ i)) → IsSubquotient σ.ρ (prinSeries ψ) →
    (∀ i j, ¬ ((∀ x, IsUnitAt w x → ψ i x = ψ j x) ∧
      ((ψ i (atFin w (unif w)) : ℂˣ) : ℂ) * normV w = (ψ j (atFin w (unif w)) : ℂˣ))) →
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)

def LocTrans : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (w : Pl F),
    (HasFixed (π.locRep w) (K1 w 0) → ∃ B, π.HasSat w B) ∧ ∀ σ, π.IsLocComp w σ → (∀ c lam, HasU w (π.locRep w) c lam → HasU w σ.ρ c lam) ∧
      ∀ ω : HChar F, (∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
        ∀ z v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((ω.loc w z : ℂˣ) : ℂ) • v

def DetCent : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (ξ : G F Ω →* (Qbar l)ˣ) (s : ℤ) (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), AttR ι r π →
    Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ s * ξ → IsOpen (ξ.ker : Set (G F Ω)) →
    ∀ ω : HChar F, (∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    ∀ w : Pl F, (∃ N : ℕ, 0 < N ∧ (((ω.loc w (atFin w (unif w)) : ℂˣ) : ℂ) * (normV w : ℂ) ^ (s + 1)) ^ N = 1) ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ x, IsUnitAt w x → ω.loc w x = 1) → Ine (F := F) A ≤ ξ.ker

def OrdPlain : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (ξ : G F Ω →* (Qbar l)ˣ) s c m a (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), OrdForm ι ξ s c m a π r →
    ∀ v σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) ∨ ∃ B, π.HasSat v B

end UpperTheory.V.Z.Win.Birth
