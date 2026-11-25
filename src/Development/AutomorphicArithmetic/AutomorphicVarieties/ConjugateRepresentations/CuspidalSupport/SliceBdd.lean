module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgebraicModuleOfVanishingBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermArchSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceAutomorphicProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceCentreOfBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceTypesOfBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicSaturationSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSlSpReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SiegelLeviBlockAevalStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SlSpPreservesGrowthAndLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem left_slSp {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  apply _root_.UpperTheory.V.Af.Fin.slLeft <;> assumption

private theorem bdd_slices {r s : ℕ} {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S) (hK : Sat S) :
    Bdd (slSp (e1 r s) (Set.range (emb (e2 r s))) (ctSp r S)) ∧
      Bdd (slSp (e2 r s) (Set.range (emb (e1 r s))) (ctSp r S)) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hK', hM⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K _ r S hS
  have hA := UpperTheory.algebraic_module_of_vanishing_block K r s _ hN (UpperTheory.constantTermSpace_centre_of_bdd K _ r S hS) ι D
  refine ⟨⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).1⟩,
    ⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).2⟩⟩
  · rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
    rw [← hM ψ hψ γ 1 (emb (e2 r s) m₂ * emb (e1 r s) m), map_mul, ← mul_assoc, ← emb_comm, blk, map_one, mul_one,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₂, rfl⟩ m
    rw [← emb_comm]
    exact hψ m m₂
  · rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
    rw [← hM ψ hψ 1 γ (emb (e1 r s) m₁ * emb (e2 r s) m), map_mul, ← mul_assoc, emb_comm, blk, map_one, one_mul,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₁, rfl⟩ m
    exact hψ m₁ m

private theorem exists_slice {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n)) {ψ : archSmooth K n} (hψ : ψ ∈ S) {g : AdelicGLn.AdelicGL K n} (hg : g ∈ Γ) :
    ∃ f ∈ slSp e Γ S, ∀ m, f.1 m = ψ.1 (g * emb e m) := by
  obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
  exact ⟨f ψ, Submodule.subset_span ⟨ψ, hψ, g, hg, hf ψ⟩, hf ψ⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.sliceBdd :
    UpperTheory.V.Cj.S.SingleBdd → UpperTheory.V.Cj.S.SliceBdd := by
  intro hB E _ _ _ r s φ hφ
  obtain ⟨S, hle, hS, hK⟩ := UpperTheory.exists_automorphic_saturation_submodule E (r + s) _ (hB E (r + s) φ hφ)
  have hmem : UpperTheory.V.Cm.smEq E (r + s) φ ∈ S :=
    hle (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self φ))
  obtain ⟨hs, -⟩ := UpperTheory.constantTerm_archSmooth E (r + s) r (UpperTheory.V.Cm.smEq E (r + s) φ) (UpperTheory.isAutomorphicForm_of_bdd_submodule E _ S hS _ hmem)
  have hψ : (⟨_, hs⟩ : GroundTheory.Automorphic.AutomorphicForm.archSmooth E (r + s)) ∈ UpperTheory.V.Af.Fin.ctSp r S :=
    Submodule.subset_span ⟨_, hmem, rfl⟩
  obtain ⟨h₁, h₂⟩ := bdd_slices hS hK
  refine ⟨Submodule.comap (UpperTheory.V.Cm.smEq E r).toLinearMap _, Submodule.comap (UpperTheory.V.Cm.smEq E s).toLinearMap _,
    h₁.mono (Submodule.map_comap_le _ _), h₂.mono (Submodule.map_comap_le _ _), fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e1 r s) (Set.range (emb (e2 r s))) _ hψ ⟨y, rfl⟩
    refine ⟨(UpperTheory.V.Cm.smEq E r).symm f, by simpa using hf, funext fun x => (hf' x).trans ?_⟩
    rw [← UpperTheory.V.Af.Fin.emb_comm]
    rfl
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e2 r s) (Set.range (emb (e1 r s))) _ hψ ⟨x, rfl⟩
    exact ⟨(UpperTheory.V.Cm.smEq E s).symm f, by simpa using hf, funext fun y => hf' y⟩
