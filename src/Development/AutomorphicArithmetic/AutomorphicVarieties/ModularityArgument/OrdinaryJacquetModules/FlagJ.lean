module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
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

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)

namespace UpperTheory.V.Z.Ord

def FlagJ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B),
    B.RingProps Λ J → ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ →
    Af.IsIrr ρ → ∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)

def BornJ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (J : Ideal B.B), B.RingProps Λ J → ENDO B ι J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h →
    x.IsRep ρ → Af.IsIrr ρ → Continuous ρ → ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → Win.Unl1 ρ w →
      Win.PotUnl ρ w ∧ ∀ π : CuspSub L n, Af.AttC ι ρ π → TU π w

end UpperTheory.V.Z.Ord

end
