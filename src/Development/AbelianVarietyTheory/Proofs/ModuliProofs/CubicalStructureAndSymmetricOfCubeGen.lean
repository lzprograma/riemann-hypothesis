module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawProduct
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.CubeGen

open GlobalTheory.AbLaw.Cube

theorem surjective_appTop {X : Scheme.{0}} (P : Over X) (e : 𝟙_ (Over X) ⟶ P) (hs : Smooth P.hom)
    (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P) :
    Function.Surjective P.hom.appTop.hom := by
  change ∀ u : Γ(P.left, P.hom ⁻¹ᵁ ⊤), ∃ a, (P.hom.app ⊤).hom a = u
  intro u
  have he : e.left ≫ P.hom = 𝟙 X := Over.w e
  have hle : (⊤ : X.Opens) ≤ e.left ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial
  have key : ∀ (g : X ⟶ X) (hg : g = 𝟙 X) (h' : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)),
      (g.appLE ⊤ ⊤ h').hom c = c := by
    rintro g rfl h' c
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    change (X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens)))).hom c = c
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hφψ : ∀ c : Γ(X, ⊤), (e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom ((P.hom.app ⊤).hom c) = c := fun c =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.Hom.comp_appLE e.left P.hom ⊤ ⊤ hle)).symm.trans
      (key _ he hle c)
  refine ⟨(e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u, ?_⟩
  have h1 := GlobalTheory.eq_one_of_appLE_section_eq_one X P e.left he hs hg ⟨hr, hab⟩ ⊤
    (1 + u - (P.hom.app ⊤).hom ((e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u)) hle
    (by rw [map_sub, map_add (f := _), map_one, hφψ]; ring)
  linear_combination -h1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def cubicalOfNormalised (s₂ : Function.Surjective (A ⊗ A).hom.appTop.hom)
    (s₃ : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (s₄ : Function.Surjective (A ⊗ A ⊗ A ⊗ A).hom.appTop.hom)
    (M : RigLB A) (t : LB.Gen (Theta A M.L)) (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  GlobalTheory.AbLaw.Cube.cubicalOfNormalised_of s₂ s₃ s₄ M t ht hn

theorem exists_gen_of_lbIso {Z : Scheme.{0}} (L : LB Z) (f : Z ⟶ Z) (h : LBIso L (L.pull f)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 Z] ![1, -1]), s.IsGen := by
  apply GlobalTheory.BiextSym.exists_gen_of_iso <;> assumption

theorem cubical_and_symmetric : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  intro X G _ _ L hsa hrg
  obtain ⟨hr, hab⟩ := hrg
  have hsm : Smooth G.hom := hsa.smooth
  have hgc : GeometricallyConnected G.hom := hsa.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth X G
  refine ⟨fun ⟨t, ht⟩ => ?_, fun hiso => ?_⟩
  · obtain ⟨t', ht', hn⟩ := exists_normalised L.isLB t ht
    obtain ⟨sm2, gi2, ab2⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G G hsm hsm hgi hgi
    obtain ⟨sm3, gi3, ab3⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G) hsm sm2 hgi gi2
    obtain ⟨sm4, gi4, ab4⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G ⊗ G) hsm sm3 hgi gi3
    have g2 : genericPoints X ⊆ abLocus (G ⊗ G) := fun x hx => ab2 ⟨hab hx, hab hx⟩
    have g3 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G) := fun x hx => ab3 ⟨hab hx, g2 hx⟩
    have g4 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G ⊗ G) := fun x hx => ab4 ⟨hab hx, g3 hx⟩
    exact ⟨cubicalOfNormalised (surjective_appTop (G ⊗ G) (lift 1 1) sm2 gi2 hr g2)
      (surjective_appTop (G ⊗ G ⊗ G) (lift 1 (lift 1 1)) sm3 gi3 hr g3)
      (surjective_appTop (G ⊗ G ⊗ G ⊗ G) (lift 1 (lift 1 (lift 1 1))) sm4 gi4 hr g4) L t' ht' hn⟩
  · exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L (exists_gen_of_lbIso L.L _ hiso)

end GlobalTheory.CubeGen
