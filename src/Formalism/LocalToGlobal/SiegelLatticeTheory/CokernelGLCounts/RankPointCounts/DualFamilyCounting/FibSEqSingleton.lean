module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLocFEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmulOfMemAutSub
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace
import Mathlib.Tactic.Lemma

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem locF_mem_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {M T Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ)
    (hM : Λ ⊓ U.restrictScalars (𝓞 K) = M) (hT : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibS h U 𝔭 M T := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ = Λ := hu
  simp only [fibS, Set.mem_setOf_eq]
  refine ⟨⟨Λ, hΛ, rfl⟩, ?_, ?_, ?_⟩
  · rw [← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ.fg h𝔭.isPrime, hu']
  · rw [← hM, LIOrb.locF_inf_locF h𝔭, G7.locF_subspace U h𝔭.isPrime]
  · rw [← hT, LIOrb.locF_inf_locF h𝔭, G7.locF_subspace (orthK h U) h𝔭.isPrime]

theorem fibS_eq_singleton (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {M T Λ₀ : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hΛ₀ : Submodule.IsLattice K Λ₀) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (he : locF 𝔭 (M ⊔ T) = locF 𝔭 Λ₀) :
    fibS h U 𝔭 M T = {locF 𝔭 (M ⊔ T)} := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ₀ = Λ₀ := hu
  have hN : dualF h 𝔭 (locF 𝔭 (M ⊔ T)) = locF 𝔭 (M ⊔ T) := by
    rw [he, ← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ₀.fg h𝔭.isPrime, hu']
  have hMU : ∀ x ∈ M, x ∈ U := fun x hx => hM.2 ▸ Submodule.subset_span hx
  have hTW : ∀ x ∈ T, x ∈ orthK h U := fun x hx => hT.2 ▸ Submodule.subset_span hx
  have hcapU : locF 𝔭 (M ⊔ T) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M :=
    locF_sup_inf hUc hMU hTW h𝔭.isPrime
  have hcapW : locF 𝔭 (M ⊔ T) ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
    rw [sup_comm]; exact locF_sup_inf hUc.symm hTW hMU h𝔭.isPrime
  ext Λ
  simp only [fibS, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨Λ₁, hΛ₁, rfl⟩, hd, hcU, hcW⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ₁ := by
      have hMT : M ⊔ T ≤ locF 𝔭 Λ₁ :=
        sup_le ((LocF.le_locF 𝔭 M).trans (hcU ▸ inf_le_left))
          ((LocF.le_locF 𝔭 T).trans (hcW ▸ inf_le_left))
      exact (LocF.locF_mono 𝔭 hMT).trans (LocF.locF_idem 𝔭 Λ₁).le
    refine le_antisymm ?_ hle
    calc locF 𝔭 Λ₁ = dualF h 𝔭 (locF 𝔭 Λ₁) := hd.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
      _ = locF 𝔭 (M ⊔ T) := hN
  · rintro rfl
    exact ⟨⟨Λ₀, hΛ₀, he.symm⟩, hN, hcapU, hcapW⟩

theorem card_glue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M)
    (hΛ₀full : Submodule.IsFullLattice K Λ₀) {T : Submodule (𝓞 K) V}
    (hT : IsLatIn (orthK h U) T) :
    Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T := by
  classical
  have hN : Submodule.IsFullLattice K (M ⊔ T) := by
    refine { toIsLattice := isLattice_sup hUc hM hT, span_eq_top := ?_ }
    rw [eq_top_iff, ← hUc.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))
  obtain ⟨s, hs⟩ := exists_locF_eq (F := F) hN hΛ₀full
  have hsing : ∀ 𝔭 ∉ s, fibS h U 𝔭.1 M T = {locF 𝔭.1 (M ⊔ T)} := fun 𝔭 h𝔭 =>
    fibS_eq_singleton hF hUc hM hT hΛ₀.1 hΛ₀.2.1 𝔭.2 (hs 𝔭 h𝔭)
  have hone : ∀ 𝔭 ∉ s, fibP h U 𝔭.1 M T = 1 := by
    intro 𝔭 h𝔭
    rw [fibP_eq, hsing 𝔭 h𝔭]
    simp
  rw [tprod_eq_prod hone, ← Finset.prod_coe_sort s]
  simp only [fibP_eq]
  rw [← Nat.card_pi]
  refine Nat.card_congr (Equiv.ofBijective
    (fun Λ 𝔭 => ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibS hF Λ.2.1.1 Λ.2.1.2.1 Λ.2.1.2.2 Λ.2.2 𝔭.1.2⟩) ⟨?_, ?_⟩)
  · rintro ⟨Λ₁, h1⟩ ⟨Λ₂, h2⟩ he
    apply Subtype.ext
    show Λ₁ = Λ₂
    refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
    by_cases hps : (⟨𝔭, h𝔭⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) ∈ s
    · exact congrArg Subtype.val (congrFun he ⟨_, hps⟩)
    · have a1 := locF_mem_fibS hF h1.1.1 h1.1.2.1 h1.1.2.2 h1.2 h𝔭
      have a2 := locF_mem_fibS hF h2.1.1 h2.1.2.1 h2.1.2.2 h2.2 h𝔭
      rw [hsing _ hps, Set.mem_singleton_iff] at a1 a2
      exact a1.trans a2.symm
  · intro τ
    obtain ⟨Λ, ⟨hΛ, hin, hout⟩, -⟩ := exists_unique_patch hK hF hN s
      (fun 𝔭 => if hp : 𝔭 ∈ s then (τ ⟨𝔭, hp⟩).1 else ⊥) (by
        intro 𝔭 hp
        simp only [dite_eq_left hp]
        obtain ⟨⟨A, hA, e⟩, -, hU, hW⟩ := (τ ⟨𝔭, hp⟩).2
        refine ⟨by rw [← e, LocF.locF_idem], A, { toIsLattice := hA, span_eq_top := ?_ }, e⟩
        have hle : locF 𝔭.1 A ≤ (Submodule.span K (A : Set V)).restrictScalars (𝓞 K) := by
          rw [← G7.locF_subspace (Submodule.span K (A : Set V)) 𝔭.2.isPrime]
          exact LocF.locF_mono 𝔭.1 (fun _ hx => Submodule.subset_span hx)
        have hNle : M ⊔ T ≤ locF 𝔭.1 A := by
          rw [e]
          exact sup_le ((LocF.le_locF 𝔭.1 M).trans (hU ▸ inf_le_left))
            ((LocF.le_locF 𝔭.1 T).trans (hW ▸ inf_le_left))
        rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le]
        exact hNle.trans hle)
    have hfib : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 Λ ∈ fibS h U 𝔭.1 M T := by
      intro 𝔭
      by_cases hp : 𝔭 ∈ s
      · rw [hin 𝔭 hp, dite_eq_left hp]
        exact (τ ⟨𝔭, hp⟩).2
      · rw [hout 𝔭 hp, hsing 𝔭 hp]
        exact Set.mem_singleton _
    have hmem : Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T := by
      refine ⟨⟨hΛ, ?_, ?_⟩, ?_⟩
      · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
        refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [G7.locF_dual hF h hΛ.fg h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace U h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace (orthK h U) h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.2
    refine ⟨⟨Λ, hmem⟩, ?_⟩
    funext 𝔭
    apply Subtype.ext
    show locF 𝔭.1.1 Λ = (τ 𝔭).1
    rw [hin 𝔭.1 𝔭.2, dite_eq_left 𝔭.2]

end Formalism.L2.SG.Pf.G8
