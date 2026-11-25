module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)

section SlopeTestRemainingChoices
open ValuativeRel GlobalTheory.StdPairSB GlobalTheory.StdPairCone

private theorem gfun_lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ν : kˣ →* ℂˣ} {ϖ : kˣ} {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  have key : ∀ x : k, x ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) ↔
      (ϖ ^ n * (ϖ ^ c)⁻¹) • x ∈ GlobalTheory.SplitWeil.cball (ϖ ^ n) := fun x => by
    rw [GlobalTheory.SplitWeil.cball_eq_smul, GlobalTheory.SplitWeil.cball_eq_smul,
      Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem, smul_smul, inv_mul_cancel_left]
  have : (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) =
      (fun q => gfun ν ϖ n q.1 q.2) ∘ fun q => (q.1, (ϖ ^ n * (ϖ ^ c)⁻¹) • q.2) := by
    ext q
    simp only [Function.comp_apply, gfun, Matrix.smul_apply, key]
  rw [this]
  exact (isLocallyConstant_gfun hϖ hν m r).comp_continuous (continuous_fst.prodMk (continuous_snd.const_smul _))

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c a a' : ℕ) :
    stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
      stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j

end SlopeTestRemainingChoices

theorem UpperTheory.stdA_stdB_mem_schwartzBruhat :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∃ m, GlobalTheory.SplitFlip.CondLE ϖ m ν) → ∀ c a a' : ℕ,
        GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ hϖ hν c a a'
  obtain ⟨n, hn⟩ := hν
  exact finiteRing_sq_sub_mul_sq_eq_of_card ν ϖ hϖ hn c a a'
