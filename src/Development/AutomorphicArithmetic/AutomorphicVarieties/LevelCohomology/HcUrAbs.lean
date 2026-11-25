module

public import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UrCard
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.urAbs :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I : Subgroup D) [I.Normal] (φ : D), (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ → (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) → finrank k (H1ur ρ I) = finrank k (H0 ρ) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ hρ I _ φ hcl hd
  have hcard := UpperTheory.V.Ws.Bl.urCard k D M ρ hρ I φ hcl hd
  let _ : Finite (H1ur ρ I) :=
    Nat.finite_of_card_ne_zero (hcard ▸ (Nat.card_pos (α := H0 ρ)).ne')
  rcases subsingleton_or_nontrivial M with hM | hM
  · let _ : Subsingleton (H1ur ρ I) := Nat.card_eq_one_iff_unique.1
      (hcard.trans (Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩)) |>.1
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    let _ : Finite k := Finite.of_injective (fun a : k => a • v) (smul_left_injective k hv)
    rw [Module.natCard_eq_pow_finrank (K := k) (V := H1ur ρ I),
      Module.natCard_eq_pow_finrank (K := k) (V := H0 ρ)] at hcard
    let _ := Fintype.ofFinite k
    apply Nat.pow_right_injective _ hcard
    change 1 < Nat.card k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
