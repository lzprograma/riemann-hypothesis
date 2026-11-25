module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ConsMemUniMIffMapSubSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM

@[expose] public section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem linkIn_uniM_eq_of_form :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (S : Set M),
      (∀ x ∈ S, φ x = 0) → ∀ τ ∈ uniM R M, ∀ v ∈ τ, φ v = 1 →
        ∃ τ' ∈ uniM R M, τ'.length + 1 = τ.length ∧
          linkIn (uniM R M) S τ = linkIn (uniM R M) S τ' := by
  intro R M _ _ _ φ S hS τ hτ v hv hφv
  classical
  have hperm := (_root_.GlobalTheory.UniSeqBasic.main R M).2.1
  have hmod := _root_.GlobalTheory.UniModVec.cons_mem_uniM_iff_map_proj R M φ v hφv
  have hp : τ.Perm (v :: τ.erase v) := List.perm_cons_erase hv
  refine ⟨(τ.erase v).map (fun x => x - φ x • v), ?_, ?_, ?_⟩
  · exact (hmod _).1 (hperm _ _ hp hτ)
  · simp [List.length_erase_of_mem hv]
    have := List.length_pos_of_mem hv
    omega
  · ext w
    simp only [linkIn, Set.mem_setOf_eq]
    refine and_congr_right fun hw => ?_
    have hpw : (τ ++ w).Perm (v :: (τ.erase v ++ w)) := hp.append_right w
    have hwfix : w.map (fun x => x - φ x • v) = w := by
      conv_rhs => rw [← List.map_id w]
      apply List.map_congr_left
      intro x hx
      simp [hS x (hw x hx)]
    constructor
    · intro h
      have h1 := (hmod _).1 (hperm _ _ hpw h)
      rwa [List.map_append, hwfix] at h1
    · intro h
      have h1 : (τ.erase v ++ w).map (fun x => x - φ x • v) ∈ uniM R M := by
        rwa [List.map_append, hwfix]
      exact hperm _ _ hpw.symm ((hmod _).2 h1)

end GlobalTheory.SeqCx

