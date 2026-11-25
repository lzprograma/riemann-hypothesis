module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

noncomputable section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.LocLanglands.InvInt

section General

variable {G : Type} [Group G] (H : Subgroup G)

def descend : (G → ℂ) →ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f (q.out)⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {H}

variable [TopologicalSpace G] [IsTopologicalGroup G]

end General

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j, Continuous fun g : GL (Fin m) k => g.val i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin m) k | g.val i j = 0}) ∩ ⋂ i, {g : GL (Fin m) k | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (hc _ _) continuous_const).inter (isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const)

end GlobalTheory.LocLanglands.InvInt
