module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

namespace GlobalTheory.ClassFin

open scoped MonoidAlgebra

private theorem subalgebra_end_eq_whole_of_isSimpleModule {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSimpleModule A V] :
    A = ⊤ := by
  have : Module.Finite (Module.End A V) V :=
    Module.Finite.of_restrictScalars_finite ℂ (Module.End A V) V
  ext T
  simp only [Algebra.mem_top, iff_true]
  let F : Module.End (Module.End A V) V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f x => by
        obtain ⟨c, rfl⟩ :=
          (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 f
        exact T.map_smul c x }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) F
  have hT : T = (a : Module.End ℂ V) :=
    LinearMap.ext fun x => (LinearMap.congr_fun ha x).symm
  exact hT ▸ a.2

theorem span_range_eq_top_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      [FiniteDimensional ℂ V], ρ.IsIrreducible → Submodule.span ℂ (Set.range ρ) = ⊤ := by
  intro G _ V _ _ ρ _ h
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range ρ)
  have hρA : ∀ g, ρ g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  have hspan : Subalgebra.toSubmodule A = Submodule.span ℂ (Set.range ρ) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    have : Set.range ρ = ((MonoidHom.mrange ρ : Submonoid (Module.End ℂ V)) : Set (Module.End ℂ V)) :=
      (MonoidHom.coe_mrange ρ).symm
    rw [this, Submonoid.closure_eq]
  let φ : Submodule A V → Subrepresentation ρ := fun M =>
    ⟨M.restrictScalars ℂ, fun g v hv => M.smul_mem (⟨ρ g, hρA g⟩ : A) hv⟩
  have : IsSimpleModule ℂ[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have : IsSimpleModule A V := by
    refine
      { toNontrivial := (Submodule.nontrivial_iff A).2 inferInstance
        eq_bot_or_eq_top := fun M => ?_ }
    rcases h.eq_bot_or_eq_top (φ M) with hM | hM
    · left
      have := congrArg Subrepresentation.toSubmodule hM
      exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 this
    · right
      have := congrArg Subrepresentation.toSubmodule hM
      exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 this
  rw [← hspan, subalgebra_end_eq_whole_of_isSimpleModule A]
  ext x
  simp

end GlobalTheory.ClassFin
