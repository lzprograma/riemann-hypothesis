module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU

namespace GlobalTheory

theorem ker_app_eq_map_appLE_of_isPullback {Y Z : Scheme.{0}} {A C : CommRingCat.{0}}
    {β : A ⟶ C} (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem isPullback_red_of_ker_app_le_map (A : Type) [CommRing A] (J : Ideal A)
    (B₀ B : Scheme.{0}) (j : B₀ ⟶ B) (s₀ : B₀ ⟶ Spec (CommRingCat.of (A ⧸ J)))
    (s : B ⟶ Spec (CommRingCat.of A)) (hj : IsClosedImmersion j) (w : j ≫ s = s₀ ≫ red J)
    (hloc : ∀ b : B, ∃ V : B.Opens, b ∈ V ∧ IsAffineOpen V ∧ RingHom.ker (j.app V).hom ≤
      J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appLE ⊤ V le_top).hom) :
    IsPullback j s₀ s (red J) := by
  have hr : IsClosedImmersion (red J) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hp : IsClosedImmersion (pullback.fst s (red J)) := inferInstance
  have hl : pullback.lift j s₀ w ≫ pullback.fst s (red J) = j := pullback.lift_fst _ _ _
  have hker : j.ker = (pullback.fst s (red J)).ker := by
    refine le_antisymm ?_ ?_
    · choose V hb hV hle using hloc
      have hcov : ⨆ b, ((⟨V b, hV b⟩ : B.affineOpens) : B.Opens) = ⊤ :=
        eq_top_iff.2 fun b _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨b, hb b⟩
      refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun b ↦ ⟨V b, hV b⟩) hcov fun b ↦ ?_
      rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
      have e := ker_app_eq_map_appLE_of_isPullback
        (β := CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective
        (IsPullback.of_hasPullback s (red J)) (hV b)
      rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at e
      exact (hle b).trans e.ge
    · have := (pullback.lift j s₀ w).le_ker_comp (pullback.fst s (red J))
      rwa [hl] at this
  have := IsClosedImmersion.isIso_of_ker_eq j (pullback.fst s (red J)) _ hl hker
  exact .of_iso_pullback ⟨w⟩ (asIso (pullback.lift j s₀ w)) hl (pullback.lift_snd _ _ _)

end GlobalTheory
