module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Mathlib.Tactic.ENatToNat
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

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp)

namespace GlobalTheory.NatFun

variable {k : Type} [CommRing k]

section Points

scoped instance sectionsAlgebra (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    Algebra k Γ(X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom.toAlgebra

theorem algebraMap_sections (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    algebraMap k Γ(X.left, U) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom := rfl

variable {X : Over (Spec (CommRingCat.of k))}
variable {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

theorem spMap_injective : Function.Injective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro φ ψ h
  have h1 : (spMap φ).left = (spMap ψ).left := by rw [h]
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))

theorem spMap_surjective : Function.Surjective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro m
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of B) m.left
  have h : CommRingCat.ofHom (algebraMap k A) ≫ φ = CommRingCat.ofHom (algebraMap k B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w m
  exact ⟨⟨φ.hom, fun c => congr(($h).hom c)⟩, Over.OverMorphism.ext hφ⟩

def affinePoint {U : X.left.Opens} (hU : IsAffineOpen U) : sp Γ(X.left, U) ⟶ X :=
  Over.homMk hU.fromSpec (by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    change hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, U)))
    rw [← h, algebraMap_sections, CommRingCat.ofHom_hom, Spec.map_comp])

end Points

section Families

abbrev AlgClass (k : Type) [CommRing k] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra k A], Prop

variable {𝒯 𝒯' : AlgClass k} {X : Over (Spec (CommRingCat.of k))}






end Families

end GlobalTheory.NatFun
