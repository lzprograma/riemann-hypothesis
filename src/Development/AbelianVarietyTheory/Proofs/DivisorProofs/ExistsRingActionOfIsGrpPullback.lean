module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.OActPull

theorem exists_oAct_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (b : OAct O G) {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hg : IsGrpPullback G' G f φ) : ∃ a : OAct O G', ∀ z, (a.act z).left ≫ φ = φ ≫ (b.act z).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (φ ≫ (b.act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ φ = φ ≫ (b.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ b.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a c => inj ?_, fun a c => inj ?_⟩, ha⟩
  · have := b.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, b.one, Category.comp_id]
  · rw [← Category.id_comp (act (a * c)), pa, pa, ← Category.id_comp (act a), pa, b.mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act c)).symm
    rw [← Category.id_comp (act (a + c)), ← Category.id_comp (act a), ← Category.id_comp (act c), pa, pa, pa, b.add]
    exact MonObj.comp_mul _ _ _

end GlobalTheory.OActPull
