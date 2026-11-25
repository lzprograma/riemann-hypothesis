module

public import GroundTheory.LocalFields.Uniqueness
public import Mathlib.FieldTheory.Galois.Basic
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

private theorem UpperTheory.Reformulated.B.MinpolyProductMap.field_case {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (y : L)
    (hy : Function.Injective fun σ : Gal(L/K) => σ y) :
    (minpoly K y).map (algebraMap K L) = ∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C (σ y)) := by
  have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_of_monic _ _ fun σ _ => Polynomial.monic_X_sub_C _)
    ((minpoly.monic hint).map _) ?_ ?_
  · refine Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C hy) fun σ => ?_
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap,
      Polynomial.aeval_algHom_apply σ, minpoly.aeval, map_zero]
  · rw [Polynomial.natDegree_map, Polynomial.natDegree_prod_of_monic _ _
      (fun σ _ => Polynomial.monic_X_sub_C _)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one]
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact minpoly.natDegree_le y

theorem UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
      [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
      [FiniteDimensional K L] [IsGalois K L] {x : ↥(ValuativeRel.valuation L).integer},
      (↥(ValuativeRel.valuation K).integer)[x] = ⊤ →
        Polynomial.map (Algebra.algebraMap ↥(ValuativeRel.valuation K).integer ↥(ValuativeRel.valuation L).integer)
            (minpoly (↥(ValuativeRel.valuation K).integer) x) =
          ∏ σ : Gal(L/K),
            (Polynomial.X -
              (Polynomial.C : ↥(ValuativeRel.valuation L).integer → Polynomial ↥(ValuativeRel.valuation L).integer)
                (((GroundTheory.LocalField.integerAlgEquiv K L :
                               Gal(L/K) →
                                 ↥(ValuativeRel.valuation L).integer ≃ₐ[↥(ValuativeRel.valuation K).integer]
                                   ↥(ValuativeRel.valuation L).integer)
                      σ :
                    ↥(ValuativeRel.valuation L).integer → ↥(ValuativeRel.valuation L).integer)
                  x)) := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ x hx
  have hinj : Function.Injective fun σ : Gal(L/K) => σ (x : L) := by
    intro σ τ h
    have h1 : ∀ z : (ValuativeRel.valuation L).integer, σ (z : L) = τ (z : L) := by
      have h2 : (GroundTheory.LocalField.integerAlgEquiv K L σ).toAlgHom =
          (GroundTheory.LocalField.integerAlgEquiv K L τ).toAlgHom := by
        refine AlgHom.ext_of_adjoin_eq_top hx ?_
        rintro _ rfl
        exact Subtype.ext h
      intro z
      exact congrArg Subtype.val (DFunLike.congr_fun h2 z)
    ext y
    rcases le_total (ValuativeRel.valuation L y) 1 with hy | hy
    · exact h1 ⟨y, hy⟩
    · have hy' : ValuativeRel.valuation L y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hy
      have h3 : σ y⁻¹ = τ y⁻¹ := h1 ⟨y⁻¹, hy'⟩
      rwa [map_inv₀, map_inv₀, inv_inj] at h3
  have hfield := UpperTheory.Reformulated.B.MinpolyProductMap.field_case (K := K) (x : L) hinj
  have hprod : (∏ σ : Gal(L/K), (Polynomial.X -
      Polynomial.C (GroundTheory.LocalField.integerAlgEquiv K L σ x))).map
        (algebraMap (ValuativeRel.valuation L).integer L) =
      (minpoly K (x : L)).map (algebraMap K L) := by
    rw [hfield, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hlift : minpoly K (x : L) ∈
      Polynomial.lifts (algebraMap (ValuativeRel.valuation K).integer K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h4 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) hprod
    simp only [Polynomial.coeff_map] at h4
    have h5 : algebraMap K L ((minpoly K (x : L)).coeff n) ∈ (ValuativeRel.valuation L).integer := by
      rw [← h4]
      exact Subtype.property _
    exact ⟨⟨_, (GroundTheory.LocalField.algebraMap_mem_integer_iff K L _).mp h5⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsIntegral.isIntegral (x : L)))
  have hcomp : (algebraMap (ValuativeRel.valuation L).integer L).comp
      (algebraMap (ValuativeRel.valuation K).integer (ValuativeRel.valuation L).integer) =
      (algebraMap K L).comp (algebraMap (ValuativeRel.valuation K).integer K) := by
    ext z
    exact GroundTheory.LocalField.coe_algebraMap_integer K L z
  have hxint : IsIntegral (ValuativeRel.valuation K).integer x := by
    refine ⟨q, hqm, ?_⟩
    apply Subtype.val_injective
    have h6 := Polynomial.hom_eval₂ q
      (algebraMap (ValuativeRel.valuation K).integer (ValuativeRel.valuation L).integer)
      (algebraMap (ValuativeRel.valuation L).integer L) x
    rw [hcomp, ← Polynomial.eval₂_map, hq] at h6
    exact h6.trans (minpoly.aeval K (x : L))
  have hmin := minpoly.isIntegrallyClosed_eq_field_fractions K L hxint
  apply Polynomial.map_injective (algebraMap (ValuativeRel.valuation L).integer L)
    Subtype.val_injective
  rw [hprod, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← hmin]
  rfl
