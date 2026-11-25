module

import ReciprocityTheory.SemistableReduction.SemiDegZA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_ne_zero_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) {v : Fin m → K}
    (hv : v ∈ Submodule.span K (L : Set (Fin m → K))) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  apply ReciprocityTheory.MultiplicativeHeights.SemiPt.clear_denom <;> assumption

theorem torsionOf_quot_lat_ne_bot : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L →
    ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  intro K _ _ m L hL x h
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_smul_mem_of_mem_span L
    (show v ∈ Submodule.span K (L : Set (Fin m → K)) by rw [hL.2]; trivial)
  have hmem : a ∈ Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) (Submodule.Quotient.mk v) := by
    rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero L).2 hav
  rw [h] at hmem
  exact ha ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
