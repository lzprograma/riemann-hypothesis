module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isEtCoord_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  intro R R' _ _ φ X X' f f' π U d t H hU ht
  refine ⟨GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback H hU, ?_⟩
  letI := φ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := R) (S := R') (σ := Fin d)
  have h₁ := (CommRingCat.isPushout_of_isPushout R R' (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R')).flip
  have hx : (MvPolynomial.eval₂Hom (algX f U) t).Etale := ht
  have key : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U),
      IsPushout (CommRingCat.ofHom (algX f U)) (CommRingCat.ofHom (algebraMap R R'))
        (π.appLE U W hle) (CommRingCat.ofHom (algX f' W)) →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale := by
    intro W hle h₂
    have e₁ : CommRingCat.ofHom (algX f U) = CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R)) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f U) t) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have e₂ : CommRingCat.ofHom (algX f' W) =
        CommRingCat.ofHom (algebraMap R' (MvPolynomial (Fin d) R')) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have hw := h₂.w
    rw [e₁, e₂] at h₂
    have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
    · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
      exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.C a))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact congrArg (fun g => (CommRingCat.Hom.hom g) a) hw
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.X a))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  have h₄ := key _ inf_le_left (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.isPushout_sections f f' π H U hU)
  have tr : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale →
      IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
    rintro W hle rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  exact tr _ _ (inf_top_eq _) h₄

end GlobalTheory.LogPair
