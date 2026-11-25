module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

namespace GlobalTheory.SmGL.CuspRow

theorem block_unique_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  intro k _ _ _ _ d V _ _ σ s' b f X _ _ ρ hσ hX hsub j j' hj hj'
  by_contra hne
  have hU : GlobalTheory.SmGL.unipRad k f ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨f ⟨j, ⟨0, hj⟩⟩, f ⟨j', ⟨0, hj'⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
    · exact ⟨f ⟨j', ⟨0, hj'⟩⟩, f ⟨j, ⟨0, hj⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
  have hs := hσ.2 s' b f hU
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor X hX
  obtain ⟨S, g, hg⟩ := hsub
  have hS : Subsingleton S.toSubmodule := inferInstance
  exact not_subsingleton _ (Function.Surjective.subsingleton hg)

end GlobalTheory.SmGL.CuspRow
