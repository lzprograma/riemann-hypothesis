module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [IsNoetherianRing A] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Smooth f := HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : GeometricallyReduced f := GlobalTheory.geometricallyReduced_of_smooth f
  have : _root_.IsReduced (CommRingCat.of A) := inferInstanceAs (_root_.IsReduced A)
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsReduced (Spec (CommRingCat.of B)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (CommRingCat.of B)).mp inferInstance

theorem GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A₀ B₀ := Algebra.Smooth.flat A₀ B₀
  have key : _root_.IsReduced (TensorProduct A₀ B₀ A) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun D hD => ?_)
    have : Algebra.FiniteType A₀ D := (Subalgebra.fg_iff_finiteType D).mp hD
    have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A₀ D
    have : _root_.IsReduced D := isReduced_of_injective D.val Subtype.val_injective
    have : _root_.IsReduced (TensorProduct A₀ D B₀) :=
      GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing D (TensorProduct A₀ D B₀)
    exact isReduced_of_injective (Algebra.TensorProduct.comm A₀ B₀ D).toRingHom
      (Algebra.TensorProduct.comm A₀ B₀ D).injective
  exact isReduced_of_injective
    ((Algebra.TensorProduct.comm A₀ A B₀).toRingHom.comp e.toRingHom)
    ((Algebra.TensorProduct.comm A₀ A B₀).injective.comp e.injective)

private theorem isReduced_of_smooth_of_isAffine_of_isReduced {Y T : Scheme.{0}} (g : Y ⟶ T) [Smooth g]
    [IsAffine T] [IsReduced T] : IsReduced Y := by
  have hι : ∀ j, Smooth (Y.affineOpenCover.f j) := fun j => inferInstance
  refine @IsReduced.of_openCover _ Y.affineOpenCover.openCover (fun j => ?_)

  have h₁ : Smooth (g ≫ T.isoSpec.hom) := inferInstance
  have h₂ : Smooth (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom) :=
    MorphismProperty.comp_mem _ _ _ (hι j) h₁
  have hs : Smooth (Spec.map (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom))) := by
    rw [Spec.map_preimage]; exact h₂
  let := (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)).hom.toAlgebra
  have : Algebra.Smooth Γ(T, ⊤) (Y.affineOpenCover.X j) := HasRingHomProperty.Spec_iff.mp hs
  have : _root_.IsReduced (Y.affineOpenCover.X j) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced Γ(T, ⊤) (Y.affineOpenCover.X j)
  show IsReduced (Spec (Y.affineOpenCover.X j))
  infer_instance

theorem GlobalTheory.isReduced_of_smooth_of_isReduced {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] [IsReduced S] : IsReduced X := by

  have hstalk : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨V, hV⟩ : ∃ V : S.affineOpens, f x ∈ (V : S.Opens) := by
      have hx : f x ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hx
    have : IsAffine (V : S.Opens) := V.2
    have hU : IsReduced (f ⁻¹ᵁ (V : S.Opens)) :=
      isReduced_of_smooth_of_isAffine_of_isReduced (f ∣_ (V : S.Opens))
    let y : (f ⁻¹ᵁ (V : S.Opens) : X.Opens) := ⟨x, hV⟩
    have := @isReduced_stalk_of_isReduced _ hU y
    exact isReduced_of_injective (Scheme.Opens.stalkIso _ y).symm.commRingCatIsoToRingEquiv
      (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X
