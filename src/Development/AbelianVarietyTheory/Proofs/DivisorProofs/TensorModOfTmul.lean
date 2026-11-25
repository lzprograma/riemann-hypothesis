module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
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

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

variable {R' : Type} [CommRing R'] {I : Ideal R'} {S : Scheme.{0}}

def crysAct (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) : O →+* Module.End R' (Crys κ t A) :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; push κ t (a.act x)
      map_one' := haveI := a.hom 1; (push_congr κ t a.one).trans (push_id κ t)
      map_mul' x y := by
        haveI := a.hom
        exact (push_congr κ t (a.mul x y)).trans (push_comp κ t _ _) }
    fun x y ↦ by
      haveI := a.hom
      haveI : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (push_congr κ t (a.add x y)).trans (push_mul κ t _ _)

theorem crysAct_apply (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) (x : O) (h : Crys κ t A) :
    crysAct κ t a x h = (haveI := a.hom x; push κ t (a.act x) h) := rfl

@[reducible] def tensorModOf {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) : Module (C ⊗[ℤ] B) H :=
  Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId C (Module.End C H)) ρ.toIntAlgHom
    fun r _ ↦ Algebra.commutes r _).toRingHom

theorem tensorModOf_tmul {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) (r : C) (x : B) (h : H) :
    (letI := tensorModOf ρ; (r ⊗ₜ[ℤ] x : C ⊗[ℤ] B) • h) = r • ρ x h := rfl

end GlobalTheory.HTSummand
