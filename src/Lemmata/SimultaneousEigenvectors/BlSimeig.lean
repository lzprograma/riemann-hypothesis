module

import Mathlib.Analysis.Complex.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

universe u_1

namespace Bl.SimultaneousEigenvectors

private theorem diagonal_commute {n : ℕ} {X : Type u_1} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : ReciprocityTheory.ChartRestriction.DS.IsGlRep A)
    (c d : Fin n) : Commute (A c c) (A d d) := by
  by_cases hcd : c = d
  · subst d; exact Commute.refl _
  · exact sub_eq_zero.mp (by simpa only [ite_eq_right hcd, ite_eq_right (Ne.symm hcd), sub_zero] using hA c c d d)

theorem goal1 {n : ℕ} {X : Type u_1} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : ReciprocityTheory.ChartRestriction.DS.IsGlRep A)
    (s : Finset (Fin n)) :
    ∀ (T : Submodule ℂ X), FiniteDimensional ℂ T → (∀ (c : Fin n) (v : X), v ∈ T → A c c v ∈ T) →
      T ≠ ⊥ → ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro T _ _ hT
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
    exact ⟨w, hw, hw0, 0, fun c hc => absurd hc (Finset.notMem_empty c)⟩
  | insert a s ha ih =>
    intro T hfd hinv hT
    have : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hT
    obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((A a a).restrict fun v hv => hinv a v hv)
    obtain ⟨⟨v, hvT⟩, hv⟩ := hl.exists_hasEigenvector
    have hv1 : A a a v = l • v := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv.1)
    have hv0 : v ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
    let T' : Submodule ℂ X := T ⊓ Module.End.eigenspace (A a a) l
    have hT' : T' ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨v, Submodule.mem_inf.mpr ⟨hvT, Module.End.mem_eigenspace_iff.mpr hv1⟩, hv0⟩
    have : FiniteDimensional ℂ T' := Submodule.finiteDimensional_of_le inf_le_left
    have hinv' : ∀ (c : Fin n) (u : X), u ∈ T' → A c c u ∈ T' := fun c u hu =>
      Submodule.mem_inf.mpr ⟨hinv c u hu.1,
        Module.End.mapsTo_genEigenspace_of_comm (diagonal_commute hA a c) l 1 hu.2⟩
    obtain ⟨w, hw, hw0, μ, hμ⟩ := ih T' inferInstance hinv' hT'
    refine ⟨w, hw.1, hw0, Function.update μ a l, fun c hc => ?_⟩
    by_cases hca : c = a
    · subst hca; rw [Function.update_self]; exact Module.End.mem_eigenspace_iff.mp hw.2
    · rw [Function.update_of_ne hca]; exact hμ c ((Finset.mem_insert.mp hc).resolve_left hca)

end Bl.SimultaneousEigenvectors
