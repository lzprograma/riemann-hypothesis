module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClassStatement
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem snd_epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp only [epsHom, DualNumber.lift_apply_apply, AlgHom.comp_apply,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_add, DualNumber.snd_mul,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.fst_eps, DualNumber.snd_eps,
    _root_.mul_one, mul_zero, add_zero, zero_add]

theorem epsHom_comp_inl {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ := by
  exact DualNumber.lift_comp_inlHom _

theorem epsHom_comp_epsMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' := by
  apply DualNumber.algHom_ext
  simp only [AlgHom.comp_apply, epsHom, EpsWeil.epsMap, DualNumber.lift_apply_eps]

theorem ptV_eq {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D]
    (x : Pt A D) : ptV v x =
      (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x : Pt (A ⊗ B) (DualNumber D)) *
      (spOver (EpsWeil.epsMap R D) ≫ CartesianMonoidalCategory.lift 1 v) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [ptV, pt0, MonObj.mul_comp, comp_lift, MonObj.comp_one]

theorem specOverOfAlgHom_comp_pointWithZeroSecondCoord {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {D D' : Type} [CommRing D] [Algebra R D] [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver φ ≫ pt0 B x : Pt (A ⊗ B) D') = pt0 B (spOver φ ≫ x : Pt A D') := by
  simp [pt0, comp_lift]

theorem cohom_sndPull_zero : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) →
    ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  intro R _ A B _ _ f hf v
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.PtExt.exists_isAdd_of_mem_primDR R (A ⊗ B) f hf
  have hc := (fv_isCoc_and_ev_eq R (A ⊗ B) f).1
  let V1 : Pt (A ⊗ B) (DualNumber R) := CartesianMonoidalCategory.lift 1 v
  refine ⟨fun D _ _ x ↦ (g (DualNumber D) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
      (spOver (EpsWeil.epsMap R D) ≫ V1) +
      fv f D (DualNumber D) (TrivSqZeroExt.inlAlgHom R D D) (pt0 B x) +
      fv f (DualNumber R) (DualNumber D) (EpsWeil.epsMap R D) V1).snd, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := hg (DualNumber D) (DualNumber D') (epsHom φ) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
    (spOver (EpsWeil.epsMap R D) ≫ V1)
  rw [← ptV_eq] at e1
  have hX : (spOver (epsHom φ) ≫ spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x :
      Pt (A ⊗ B) (DualNumber D')) =
      spOver (TrivSqZeroExt.inlAlgHom R D' D') ≫ pt0 B (spOver φ ≫ x : Pt A D') := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_inl, ← spOver_comp, Category.assoc, specOverOfAlgHom_comp_pointWithZeroSecondCoord]
  have hV : (spOver (epsHom φ) ≫ spOver (EpsWeil.epsMap R D) ≫ V1 :
      Pt (A ⊗ B) (DualNumber D')) = spOver (EpsWeil.epsMap R D') ≫ V1 := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_epsMap]
  rw [hX, hV] at e1
  have c1 := hc D (DualNumber D) (DualNumber D') (TrivSqZeroExt.inlAlgHom R D D) (epsHom φ) (pt0 B x)
    (sm_whole _)
  have c2 := hc D D' (DualNumber D') φ (TrivSqZeroExt.inlAlgHom R D' D') (pt0 B x) (sm_whole _)
  rw [epsHom_comp_inl, c2, specOverOfAlgHom_comp_pointWithZeroSecondCoord] at c1
  have c3 := hc (DualNumber R) (DualNumber D) (DualNumber D') (EpsWeil.epsMap R D) (epsHom φ) V1 (sm_whole _)
  rw [epsHom_comp_epsMap] at c3
  have s1 := congrArg TrivSqZeroExt.snd e1
  have s2 := congrArg TrivSqZeroExt.snd c1
  have s3 := congrArg TrivSqZeroExt.snd c3
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, snd_epsHom,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_inl, zero_add] at s1 s2 s3
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, neg_zero, add_zero, TrivSqZeroExt.snd_add, map_add (f := _)]
  linear_combination -s1 - s2 - s3

end GlobalTheory.PtExt
