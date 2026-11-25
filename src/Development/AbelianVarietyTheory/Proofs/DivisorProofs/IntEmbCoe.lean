module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def IsActPull {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] (i' : OAct O G') (i : OAct O G)
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  IsGrpPullback G' G f φ ∧ ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left

def IsCover (k : Type) [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)] (π : C' ⟶ C) : Prop :=
  IsFinite π ∧ Surjective π ∧ π ≫ strHom k C = strHom k C'

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Defs

def Splits (O k : Type) [CommRing O] [Field k] : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (τ : κ → (O →+* k)), IsSplitBy τ

section Lemmas

variable {O : Type} [CommRing O]

theorem IsActPull.comp {S S' S'' : Scheme.{0}} {G'' : Over S''} [GrpObj G''] {G' : Over S'} [GrpObj G'] {G : Over S}
    [GrpObj G] {i'' : OAct O G''} {i' : OAct O G'} {i : OAct O G} {g : S'' ⟶ S'} {f : S' ⟶ S} {φ' : G''.left ⟶ G'.left}
    {φ : G'.left ⟶ G.left} (h' : IsActPull i'' i' g φ') (h : IsActPull i' i f φ) : IsActPull i'' i (g ≫ f) (φ' ≫ φ) :=
  ⟨h'.1.comp h.1, fun a => by rw [← Category.assoc, h'.2, Category.assoc, h.2, Category.assoc]⟩

end Lemmas

end GlobalTheory.CurveRootGeometry
