module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.SharedLemmas.CocycleFiniteIndex

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.z1fDesc :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (H : Subgroup G) [H.Normal] [H.FiniteIndex], ∀ c ∈ Z1 ρ, (c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ ↔ (fun h : H => c h) ∈ UpperTheory.V.Loc.finiteCocycles (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ A _ _ V _ _ _ _ _ _ _ _ _ ρ H _ _ c hc
  constructor
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp continuous_subtype_val, fun g h => hc.2 g h⟩, x, fun h => hx h⟩
  · rintro ⟨-, x, hx⟩
    refine ⟨hc, ?_⟩
    refine Formalism.SharedLemmas.cocycle_coboundary_of_finiteIndex_sub (k := ℚ_[l]) (fun g => (actC φ ρ g).restrictScalars ℚ_[l]) ?_
      (fun g => c g ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ H x (fun h hh => hx ⟨h, hh⟩)
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add (f := _), hu, hv]
    · intro g h
      simp [actC, hc.2 g h, add_tmul]
