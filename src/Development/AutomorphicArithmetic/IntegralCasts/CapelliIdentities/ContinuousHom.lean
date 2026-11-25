module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs

@[expose] public section

theorem UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom :
    ∀ {Γ M : Type} [Group Γ]
    [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M] (f : Γ →* Mˣ),
    (Continuous fun (g : Γ) ↦ (↑((f : Γ → Mˣ) g) : M)) → Continuous (⇑f : Γ → Mˣ) := by
  intro Γ M _ _ _ _ _ f h
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  refine (h.comp continuous_inv).congr fun g => ?_
  simp only [Function.comp_apply, map_inv]
