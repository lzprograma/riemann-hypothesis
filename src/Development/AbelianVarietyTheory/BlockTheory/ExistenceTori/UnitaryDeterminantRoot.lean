module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
open scoped TensorProduct

section Adeles

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]

def IsRealIn : Prop := ∀ a : F, cc (algebraMap F E a) = algebraMap F E a

abbrev AdE : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

def IsIntF (a : FiniteAdeleRing (𝓞 F) F) : Prop := ∀ v, a v ∈ v.adicCompletionIntegers F

variable {E}

def diagE : E →+* AdE F E := Algebra.TensorProduct.includeRight.toRingHom

def vecA {r : ℕ} (v : Fin r → E) : Fin r → AdE F E := fun i => diagE F (v i)

def latHat {r : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ x : La, z = fun i => a ⊗ₜ ι x i}

variable [hF : Fact (IsRealIn F E)]

def conjF : E →ₐ[F] E where
  toRingHom := (IsCMField.complexConj E).toRingEquiv.toRingHom
  commutes' := hF.out

def conjA : AdE F E →ₐ[F] AdE F E := Algebra.TensorProduct.map (AlgHom.id F _) (conjF F)

variable {F}

end Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r : ℕ}

section Clauses

variable {La' : Type} [AddCommGroup La'] [Module (𝓞 E) La']

def LatAt (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∀ v : Fin r → E, (∃ b, φ b = v) ↔ ∃ z ∈ latHat F ι, vecA F v = g.mulVec z

end Clauses

section Value

variable [Fact (IsRealIn F E)] {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def sig0 : c.F →+* ℂ := c.F.val.toRingHom

variable {Xo c}

variable (Xo c)

end Value

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
