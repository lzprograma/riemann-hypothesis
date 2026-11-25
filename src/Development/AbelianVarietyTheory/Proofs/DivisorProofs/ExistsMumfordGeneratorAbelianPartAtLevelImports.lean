module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVCat

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory.EndRosati

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem mφ_comp {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂)
    {T : Over S} (x y : T ⟶ H₁) (k : MK) :
    (lift x y).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr)
        (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₁ ![x, y] I.down).left ≫ coprod.inl) k := by
  rcases k with I | I
  · have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) ≫ psum H₂ (x2 H₂) I.down =
        psum H₂ ![x ≫ a, y ≫ b] I.down := by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr =
      (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr
    rw [← e]
    simp only [Over.comp_left, Category.assoc]
  · have e : lift x y ≫ psum H₁ (x2 H₁) I.down = psum H₁ ![x, y] I.down := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl = (psum H₁ ![x, y] I.down).left ≫ coprod.inl
    rw [← e]
    simp only [Over.comp_left, Category.assoc]

theorem mφ_push {S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} [GrpObj E₁] [IsCommMonObj E₁] [GrpObj E₂]
    [IsCommMonObj E₂] {A₁ A₂ : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂)
    (hm₁ : ∀ {T : Over S'} (x y : T ⟶ E₁), push p₁ (x * y) = push p₁ x * push p₁ y)
    (hm₂ : ∀ {T : Over S'} (x y : T ⟶ E₂), push p₂ (x * y) = push p₂ x * push p₂ y)
    {a' b' : E₁ ⟶ E₂} {a b : A₁ ⟶ A₂} (ha : push p₂ a' = p₁ ≫ a) (hb : push p₂ b' = p₁ ≫ b)
    {T : Over S'} (x y : T ⟶ E₁) (k : MK) :
    (lift (push p₁ x) (push p₁ y)).left ≫ mφ A₁ A₂ a b k =
      (lift x y).left ≫ mφ E₁ E₂ a' b' k ≫ coprod.map p₁.left p₂.left := by
  let ρ₁ : (T ⟶ E₁) →* ((Over.map j).obj T ⟶ A₁) :=
    MonoidHom.mk' (push p₁) fun x y => hm₁ x y
  let ρ₂ : (T ⟶ E₂) →* ((Over.map j).obj T ⟶ A₂) :=
    MonoidHom.mk' (push p₂) fun x y => hm₂ x y
  have pa : ∀ (z : T ⟶ E₁) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}, push p₂ c' = p₁ ≫ c → push p₂ (z ≫ c') = push p₁ z ≫ c :=
    fun z c' c h => by
      simp only [push, Functor.map_comp, Category.assoc] at h ⊢
      rw [h]
  rw [← Category.assoc, mφ_comp, mφ_comp]
  rcases k with I | I
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₂ ![x ≫ a', y ≫ b'] I.down
    have e' : (fun i => ρ₂ ((![x ≫ a', y ≫ b'] : Fin 2 → (T ⟶ E₂)) i)) = ![push p₁ x ≫ a, push p₁ y ≫ b] := by
      funext i
      fin_cases i
      · exact pa x ha
      · exact pa y hb
    rw [e'] at e
    show (psum A₂ ![push p₁ x ≫ a, push p₁ y ≫ b] I.down).left ≫ coprod.inr =
      ((psum E₂ ![x ≫ a', y ≫ b'] I.down).left ≫ coprod.inr) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inr_map, ← Category.assoc]
    rfl
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₁ ![x, y] I.down
    have e' : (fun i => ρ₁ ((![x, y] : Fin 2 → (T ⟶ E₁)) i)) = ![push p₁ x, push p₁ y] := by
      funext i
      fin_cases i <;> rfl
    rw [e'] at e
    show (psum A₁ ![push p₁ x, push p₁ y] I.down).left ≫ coprod.inl =
      ((psum E₁ ![x, y] I.down).left ≫ coprod.inl) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inl_map, ← Category.assoc]
    rfl

end GlobalTheory.HomMum
