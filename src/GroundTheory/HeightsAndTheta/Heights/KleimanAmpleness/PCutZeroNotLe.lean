module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutZeroNotLeSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZeroIdealChart
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutDimLower

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutZeroNotLeAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_zeroIdeal_div_eq (D : SubFamily S x Ω) (hfg : ∀ K, (D.sub K).FG) (I : Chart x)
    {σ y : Ω} (hσ : σ ∈ D.sub I) (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∃ (g t : Poly S N) (n : ℕ), g ∈ zeroIdeal D.toSubSystem σ ∧ t ∈ monos I.1 ∧
      g.IsHomogeneous n ∧ t.IsHomogeneous n ∧ σ * y = aeval x g / aeval x t := by
  classical

  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy σ hσ
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * σ * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  obtain ⟨U, hUm, dU, hUh, hUK⟩ := exists_monos_mul_mem_twistMod_all_subFamily D hfg I y hy
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ zeroIdeal D.toSubSystem σ := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]
      ring
  refine ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end CutZeroNotLeAux

theorem CutZeroNotLe.proof : CutZeroNotLe.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp L s _ hs ⟨I, hI⟩
  have hsI : s ∈ L.sub I := (Submodule.mem_iInf _).mp hs I
  obtain ⟨P, hP⟩ := L.invertible I

  have hex : ∃ y ∈ P, s * y ∉ idealMod pp I := by
    by_contra hcon
    push Not at hcon
    apply hI
    rw [SubSystem.twist_sub_eq_mul_sub]
    have hle : Submodule.span (chartRing k x I) {s} * P ≤ idealMod pp I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (hcon b hb)
    have hmem : s ∈ Submodule.span (chartRing k x I) {s} * P * L.sub I := by
      rw [mul_assoc, mul_comm P, hP, mul_one]
      exact Submodule.mem_span_singleton_self s
    exact mul_le_mul' hle le_rfl hmem
  obtain ⟨y, hyP, hsy⟩ := hex
  have hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := by
    intro δ hδ
    have h := Submodule.mul_mem_mul hδ hyP
    rw [hP] at h
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp h
    rw [mul_comm, ← ha]
    exact a.2
  obtain ⟨g, t, n, hg, ht, hgn, htn, hst⟩ := exists_zeroIdeal_div_eq L.toSubFamily L.fg I hsI hy
  refine ⟨g, hg, fun hgp => hsy ?_⟩
  rw [hst]
  exact Submodule.subset_span ⟨g, t, n, hgp, ht, hgn, htn, rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
