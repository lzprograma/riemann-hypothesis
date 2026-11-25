module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.SqPull

theorem tensor_isPullback {S : Scheme.{0}} (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback _ _

theorem sq_of_grpPullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  intro S S₀ f B _ B₀ _ i h
  obtain ⟨hP, hM⟩ := h
  let T : Over S₀ := B₀ ⊗ B₀
  have hw : ∀ x : T ⟶ B₀, (x.left ≫ i) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
    intro x
    rw [Category.assoc, hP.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((fst B₀ B₀).left ≫ i) (hw _)
  let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((snd B₀ B₀).left ≫ i) (hw _)
  have h1 : (lift x₀ y₀).left ≫ (fst B B).left = (fst B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift x₀ y₀).left ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨(lift x₀ y₀).left, ?_, ?_, h1, h2⟩
  · have outer : IsPullback ((snd B₀ B₀).left ≫ i) (fst B₀ B₀).left B.hom (B₀.hom ≫ f) :=
      IsPullback.paste_horiz (tensor_isPullback B₀ B₀).flip hP
    have sq : IsPullback (lift x₀ y₀).left (fst B₀ B₀).left (fst B B).left i := by
      refine IsPullback.of_right (h₁₂ := (snd B B).left) (v₁₃ := B.hom) (h₂₂ := B.hom) ?_ h1
        (tensor_isPullback B B).flip
      rw [h2, hP.w]
      exact outer
    exact IsPullback.paste_vert sq hP
  · have := hM T (fst B₀ B₀) (snd B₀ B₀) x₀ y₀ rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at this
    exact this

end GlobalTheory.SqPull
