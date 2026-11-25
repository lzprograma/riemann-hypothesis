module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
public import Mathlib.Analysis.Calculus.Deriv.ZPow

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory


section

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g') {K : Type} [Fintype K] (f : K → (A ⟶ A'))
  (F : K → ((Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))) (ε : K → ℤ)

def linCombUnif (h : ∀ k z, u'.ex (F k z) = u.ex z ≫ f k) :
    HolUnif A (LB.LinComb L' (fun k => (f k).left) ε) g :=
  have hl : ∀ k z, (u'.ex (F k z)).left = (u.ex z).left ≫ (f k).left := fun k z => by
    rw [h k z]; rfl
  have hc : ∀ (j : K → L'.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ LB.wchart L' (fun k => (f k).left) j →
      ∀ k, ⊤ ≤ (u'.ex (F k z)).left ⁻¹ᵁ L'.U (j k) := fun j z hz k => by
    rw [hl k z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' (fun k => (f k).left) j).1 hz k
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun (j : K → L'.ι) z => ∏ k, u'.fr (j k) (F k z) ^ ε k
    fr_hol := fun j z hz => by
      classical
      exact (HasFDerivWithinAt.finsetProd (u := Finset.univ)
        (g := fun k (w : Fin g → ℂ) => u'.fr (j k) (F k w) ^ ε k) fun k _ =>
        ((DifferentiableOn.zpow ((u'.fr_hol (j k)).comp
          (LinearMap.toContinuousLinearMap (F k)).differentiable.differentiableOn
          fun w hw => hc j w hw k)
          (Or.inl fun w hw => u'.fr_ne _ _ (hc j w hw k))) z hz).hasFDerivWithinAt
        ).differentiableWithinAt
    fr_ne := fun j z hz => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u'.fr_ne _ _ (hc j z hz k))
    fr_compat := fun j j' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf (u.ex z).left _ _).1 hz
      have e := CubeValues.val_linComb (u.ex z).left valAt'_rules L' (fun k => (f k).left) ε j j' h1 h2
      refine Eq.trans ?_ (congrArg (· * ∏ k, u'.fr (j' k) (F k z) ^ ε k) e.symm)
      show _ = (∏ k, _) * _
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← mul_zpow, ← hl k z]
      exact congrArg (· ^ ε k) (u'.fr_compat (j k) (j' k) (F k z)
        ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩)) }

end

theorem exists_holUnif_linComb : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (K : Type) [Fintype K] (f : K → (A ⟶ A')) (F : K → ((Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))) (ε : K → ℤ), (∀ k z, u'.ex (F k z) = u.ex z ≫ f k) → ∃ u₁ : HolUnif A (LB.LinComb L' (fun k => (f k).left) ε) g, u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ ∀ (j : K → L'.ι) z, u₁.fr j z = ∏ k, u'.fr (j k) (F k z) ^ ε k := by
  intro A A' _ _ L L' g g' u u' K _ f F ε hF
  refine ⟨linCombUnif u u' f F ε hF, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro j z
    rfl

end GlobalTheory
