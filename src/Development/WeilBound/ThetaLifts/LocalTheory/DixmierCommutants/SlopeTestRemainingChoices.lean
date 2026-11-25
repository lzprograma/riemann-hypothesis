module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.TopOfMap
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

section
open Polynomial

theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 :=
  _root_.GlobalTheory.dixmier_commutant_scalar ι V ρ hrank hirr T hT

end

section
open PositivityTheory.KCo GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem irrF' (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {ν α : kˣ →* ℂˣ} (hnd : n ≤ d) (hν : USm ν)
    (N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)) (hA : augF n d ν α ≤ N)
    (hN : ∀ h : GL (Fin d) k, ∀ Φ ∈ N, Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) → omB ν α 1 h Φ ∈ N) :
    (∀ Φ, Full Φ → Φ ∈ N) ∨ ∀ Φ ∈ N, Full Φ → Φ ∈ augF n d ν α := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have hμ : IsSmoothChar ν⁻¹ := IsSmoothChar.inv hν.2
  obtain ⟨E⟩ := _root_.GlobalTheory.CompanionTheory.ThetaGLLen.fibStr k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ
  have hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤
      (augF n (n + t) ν α).comap extZ := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, rfl⟩
    refine Submodule.subset_span ⟨g, extZ φ, ⟨extZ_mem φ, fun Y hY => extZ_neg φ (by rwa [rank_transpose])⟩, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    refine funext fun Y => (extZ_act _ g 1 φ Y).trans ?_
    have n1 : nabs k 1 = 1 := by simp [nabs]
    simp [omB, omChar, apow, val_absPow, n1])
  rcases irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono hA)) (by
    intro h φ hf
    have h1 := hN (invT h) _ hf (extZ_mem φ)
    rw [Submodule.mem_comap]
    have c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))
    convert N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) /
      ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1
    funext Y
    have e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) *
        extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val) := by
      simp [omB, apow, nabs]
    rw [extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h
  · refine Or.inl fun Φ hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact (h ▸ Submodule.mem_top : φ ∈ N.comap extZ)
  · refine Or.inr fun Φ hm hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact hR (h hm)

end

theorem rank_SB (V : Type) [TopologicalSpace V] [SecondCountableTopology V] [T2Space V] :
    Module.rank ℂ (GlobalTheory.WeilM.SB V) ≤ Cardinal.aleph0 := by
  classical
  have hc : {K : Set V | IsCompact K ∧ IsOpen K}.Countable := by
    refine ((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis V)).image Set.sUnion).mono ?_
    rintro K ⟨h1, h2⟩
    obtain ⟨S, hS, rfl⟩ := (TopologicalSpace.isBasis_countableBasis V).open_eq_sUnion h2
    obtain ⟨T, hT, hf, hcov⟩ := h1.elim_finite_subcover_image (b := S) (c := id)
      (fun s hs => (TopologicalSpace.isBasis_countableBasis V).isOpen (hS hs)) (by rw [Set.sUnion_eq_biUnion]; rfl)
    refine ⟨T, ⟨hf, hT.trans hS⟩, subset_antisymm (Set.sUnion_mono hT) ?_⟩
    rw [Set.sUnion_eq_biUnion (s := T)]; exact hcov
  have hle : GlobalTheory.WeilM.SB V ≤ Submodule.span ℂ ((fun K : Set V => K.indicator (1 : V → ℂ)) '' {K | IsCompact K ∧ IsOpen K}) := by
    intro f hf
    have hfin : (f '' tsupport f).Finite := by
      haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2.isCompact
      have h2 := (hf.1.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite
      rwa [Set.range_comp, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h2
    have e : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : V → ℂ) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_eq_single (f y)]
      · simp
      · intro c _ hc
        simp [hc.symm]
      · intro h
        have : f y = 0 := by
          by_contra h0
          exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨y, subset_tsupport _ h0, rfl⟩⟩)
        simp [this]
    rw [e]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, hf.1 _⟩, rfl⟩)
    refine hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber c).1 fun y hy => subset_tsupport _ ?_
    rw [Function.mem_support, show f y = c from hy]
    exact (Finset.mem_erase.1 hc).1
  exact (Submodule.rank_mono hle).trans ((rank_span_le _).trans (Cardinal.mk_le_aleph0_iff.2 (hc.image _).to_subtype))

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
