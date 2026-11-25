module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympUnip

open GlobalTheory.SympChange GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Ring

variable {R κ : Type} [CommRing R] [Fintype κ]

def mulR (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

end Ring

variable {F : Type} [Field F] [NumberField F]

theorem eventually_integral (z : Af F) : ∀ᶠ v : Pl F in cofinite, evalV F v z ∈ v.adicCompletionIntegers F := z.2

theorem eventually_evFin (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  eventually_integral (sndA F a)

theorem exists_finite_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) : ∃ I : Set (Pl (F := F)), I.Finite ∧
    ∀ z : Af F, (∀ v, evalV F v z ∈ v.adicCompletionIntegers F) → (∀ v ∈ I, evalV F v z = 0) → finChar ψ z = 1 := by
  let f : (∀ v : Pl (F := F), v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  have hf : Continuous f := RestrictedProduct.isEmbedding_structureMap.continuous
  have hlc : IsLocallyConstant (fun y => finChar ψ (f y)) := (finChar_isLocallyConstant ψ hψ).comp_continuous hf
  have h0 := hlc.eventually_eq 0
  rw [Filter.Eventually, nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, hI, t, ht, hs⟩ := h0
  refine ⟨I, hI, fun z hz hz0 => ?_⟩
  have hy : (fun v : Pl F => (⟨evalV F v z, hz v⟩ : v.adicCompletionIntegers F)) ∈ I.pi t := fun v hv => by
    have : (⟨evalV F v z, hz v⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (hz0 v hv)
    exact Set.mem_of_eq_of_mem this (mem_of_mem_nhds (ht v))
  have h1 : finChar ψ z = finChar ψ 0 := hs hy
  rw [h1, AddChar.map_zero_eq_one]

theorem finChar_eq_finprod (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (z : Af F) :
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evalV F v z)).Finite ∧
      finChar ψ z = ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evalV F v z) := by
  classical
  obtain ⟨I, hI, h⟩ := exists_finite_trivial ψ hψ
  have hT : (I ∪ {v | evalV F v z ∉ v.adicCompletionIntegers F}).Finite := hI.union (eventually_integral z)
  have hloc : ∀ (v : Pl (F := F)) (y : Fv F v), GlobalTheory.LatVac.psiAt ψ v y = finChar ψ (singleFin v y) := fun _ _ => rfl
  have hsub : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evalV F v z)) ⊆ hT.toFinset := by
    intro v hv
    by_contra hn
    simp only [Set.Finite.coe_toFinset, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    refine hv ((hloc v _).trans (h _ (fun u => ?_) fun u hu => ?_))
    · by_cases huv : u = v
      · subst huv
        rw [evalV_singleFin_self]; exact hn.2
      · rw [evalV_singleFin_ne huv]; exact zero_mem _
    · exact evalV_singleFin_ne (fun e : u = v => hn.1 (e ▸ hu)) _
  refine ⟨hT.toFinset.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  set s : Af F := ∑ v ∈ hT.toFinset, singleFin v (evalV F v z) with hs
  have hev : ∀ u, evalV F u s = if u ∈ hT.toFinset then evalV F u z else 0 := by
    intro u

    rw [hs, map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single_of_mem u hu fun v _ hv => evalV_singleFin_ne hv.symm _, evalV_singleFin_self]
    · exact Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _
  have h1 : finChar ψ (z - s) = 1 := by
    refine h _ (fun u => ?_) fun u hu => ?_
    · rw [map_sub, hev]
      split_ifs with hu
      · rw [sub_self]; exact zero_mem _
      · simp only [Set.Finite.mem_toFinset, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hu
        rw [sub_zero]; exact hu.2
    · rw [map_sub, hev, ite_eq_left (hT.mem_toFinset.2 (Or.inl hu)), sub_self]
  have h2 : ∀ T : Finset (Pl (F := F)), finChar ψ (∑ v ∈ T, singleFin v (evalV F v z)) =
      ∏ v ∈ T, GlobalTheory.LatVac.psiAt ψ v (evalV F v z) := by
    intro T
    induction T using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
    | insert a T ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih, hloc]
  rw [← h2, ← hs, ← one_mul (finChar ψ s), ← h1, ← AddChar.map_add_eq_mul, sub_add_cancel]

theorem psiAt_isLocallyConstant (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) :
    IsLocallyConstant (GlobalTheory.LatVac.psiAt ψ v) :=
  (finChar_isLocallyConstant ψ hψ).comp_continuous (continuous_singleFin v)

end GlobalTheory.SympUnip

end
