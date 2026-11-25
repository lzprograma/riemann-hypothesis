module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Pointwise

private theorem frob_of_smul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  apply _root_.GlobalTheory.WeilDeligne.MonodromyThm.isFrob_conj <;> assumption

private theorem one_lt_normV' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : 1 < normV w := by
  simpa only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] using
    NumberField.HeightOneSpectrum.one_lt_absNorm w

private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := by
    rw [normV, Nat.card_eq_fintype_card]
  rw [e]
  by_contra hlt
  refine Polynomial.X_pow_sub_X_ne_zero (R := 𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [Polynomial.natDegree_X_pow_sub_X hq, Finset.card_univ]
    exact not_le.1 hlt

theorem UpperTheory.frobenius_sign_compatibility :
    UpperTheory.V.Af.Bc.SignFrob := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι δ hδ w hur A' hA'
  refine ⟨hur A' hA', fun σ' hσ' => ?_⟩
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  have hv : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hv hA'
  have hσ := frob_of_smul hσ'
  have e : δ σ' = δ (g⁻¹ * σ' * g) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  rw [map_inv, e]
  generalize g⁻¹ * σ' * g = σ at hσ
  split_ifs with hq
  · obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hφ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (res F Ω E φ) := by
      rw [← hq]
      exact ⟨hφ.1, hφ.2⟩
    have h1 := hur A hv _ (inv_mul_mem_Ine_of_isFrob hσ hφ')
    rw [map_mul, (hδ.1 _).2 ⟨φ, rfl⟩, mul_one, map_inv] at h1
    rw [h1]; simp
  · rcases hδ.2 σ with h1 | h1
    · exfalso
      obtain ⟨ψ, rfl⟩ := (hδ.1 σ).1 h1
      have hle : normV w ≤ normV (w.under (𝓞 F)) := by
        refine normV_le w (one_lt_normV' _) fun x => ?_
        rw [← hA]
        have hx : A.valuation (algebraMap E Ω x) ≤ 1 := by
          rw [A.valuation_le_one_iff]
          have hi : IsIntegral ℤ (algebraMap E Ω x) := x.isIntegral_coe.algebraMap
          obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
          rw [← hy]
          exact y.2
        have h2 := hσ.2 _ hx
        have h3 : res F Ω E ψ (algebraMap E Ω x) = algebraMap E Ω x := ψ.commutes x
        rw [h3] at h2
        simpa using h2
      refine hq (le_antisymm hle ?_)
      have h4 := one_lt_normV' w
      rw [_root_.GlobalTheory.DelEps.WeilRes.normV_eq_pow (K := F) w] at h4 ⊢
      refine Nat.le_self_pow (fun h0 => ?_) _
      rw [h0] at h4
      simp at h4
    · rw [h1]; simp
