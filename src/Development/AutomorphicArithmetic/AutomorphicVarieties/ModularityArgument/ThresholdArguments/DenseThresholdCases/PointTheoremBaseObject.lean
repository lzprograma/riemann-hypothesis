module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointPurity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.CuspRep
open Formalism.MainNotions.N Polynomial
namespace UpperTheory.V.W
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
variable {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid (HidaSetting.Lev.frame V) c.O n}
namespace UniversalOrdinaryDeterminantRing
variable (B : UniversalOrdinaryDeterminantRing r)
variable {B}
variable (B) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)
def PointTheoremBaseObject : Prop :=
  ∀ (x : B.Pt) (h : HidaSetting.Wt s n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x
structure HidaPropsAlt (Λ : LamObj r) : Prop where
  ring : B.RingProps Λ J
  dense : B.Dense J
  pt : B.PointTheoremBaseObject ι J
  end1 : B.arithmeticPointPurityDense ι J
  end2 : B.arithmeticPointClassicalityDense ι J
  twist : B.TwistOk J
structure ModularAlt (Λ : LamObj r) : Prop extends toHidaProps : B.HidaPropsAlt ι J Λ where
  p1 : B.P1core J
  p3 : B.P3core J
end UniversalOrdinaryDeterminantRing
end U
def ModUAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 1 ≤ n → ∀ (r : Resid (HidaSetting.Lev.frame V) c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.ModularAlt ι J Λ
end UpperTheory.V.W
end
end
