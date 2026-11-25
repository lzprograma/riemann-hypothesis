module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem expT_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → (∀ e, U'.ExpandsAt e k σ f) → U.ExpT (𝟙_ _) k σ' f' := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨S, hS⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U' e k σ f (hE e)
  refine ⟨S, fun Z x rG rB h1 h2 _ z JG J hJG hJ => ?_⟩
  obtain ⟨h₀, h₁⟩ := hS Z x z J hJ
  clear hS hE
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  cases U'
  dsimp only at hL hgt hw
  subst hL hgt
  cases hw
  cases hσ
  have eB : ∀ α, sval (f' α) rB z J = sval (f α) (x ≫ (U.gt e).pG.left) z J := fun α => by
    rw [hB α Z rB z J hJ, h2]
  refine ⟨fun α hα => (eB α).trans (h₀ α hα), ?_⟩
  have H := h₁ (JG (x ≫ (fstG I e G).left)) (hJG (x ≫ (fstG I e G).left))
  rw [hG Z rG z JG hJG, h1, Finset.sum_congr rfl fun α _ => congrArg (· * _) (eB α)]
  refine Eq.trans ?_ H
  rw [Units.val_pow_eq_pow_val, sval_of σ₀ _ z JG (fun _ => JG (x ≫ (fstG I e G).left)) (fun _ => by rw [Category.comp_id])]
  rfl

end GlobalTheory.UU
