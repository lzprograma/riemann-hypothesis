module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
noncomputable section
namespace GlobalTheory.ZH

theorem labelled_torsion_pull {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over B') {E : Over B}
    (U : Over.mk (T.hom ≫ f) ⟶ E) {Γ : Type} [Add Γ] (pt : Γ → (E ⟶ G)) (m : ℕ)
    (hadd : ∀ a b, pt (a + b) = pt a * pt b) (htors : ∀ a, pt a ^ m = 1)
    (hbij : ∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ m = 1 → ∃! a, U ≫ pt a = z) :
    ∃ x : Γ → (T ⟶ G'), (∀ a, (x a).left ≫ φ = U.left ≫ (pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧
      Function.Injective x ∧ ∀ z : T ⟶ G', z ^ m = 1 → ∃ a, z = x a := by
  have hinj : Function.Injective (pushHom h T) := fun x y e => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) e
    · rw [Over.w, Over.w]
  have hsurj : Function.Surjective (pushHom h T) := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  choose x hx using fun a => hsurj (U ≫ pt a)
  refine ⟨x, fun a => congrArg (fun z => z.left) (hx a), fun a b => hinj ?_, fun a b e => ?_, fun z hz => ?_⟩
  · rw [map_mul, hx, hx, hx, hadd, MonObj.comp_mul]
  · have ht : (U ≫ pt a) ^ m = 1 := by
      have := map_pow (preHom U) (pt a) m
      rw [htors, map_one] at this
      exact this.symm
    exact (hbij _ ht).unique rfl (by rw [← hx, ← hx, e])
  · obtain ⟨a, ha, -⟩ := hbij (pushHom h T z) (by rw [← map_pow, hz, map_one])
    exact ⟨a, hinj (by rw [hx, ha])⟩

theorem utest_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  intro o Ω _ _ _ S ρ p _ y₀ u
  have e : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull u.cart (TFK (R := u.V) (PadicAlgCl p))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK :) (by simp)) ρ.pt (S.r * S.N) ρ.pt_add
    (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (PadicAlgCl p) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

end GlobalTheory.ZH
end
