module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible

@[expose] public section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.BridgeCPX
open scoped InnerProductSpace

open scoped Matrix.Norms.Elementwise

namespace Formalism.L2.SG.HCReprodM

def HCReprodDSc : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ w ∈ lowKSub ε lam σ, ∃ α : Formalism.REAL.UJ ε → ℂ, Continuous α ∧ HasCompactSupport α ∧
      Integrable (fun g => α g • σ (uMat g) w) (Formalism.REAL.muG ε) ∧
      ∫ g, α g • σ (uMat g) w ∂(Formalism.REAL.muG ε) = w

def HCReprodDSm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ w ∈ lowKSub ε lam σ, ∃ (α : Formalism.REAL.UJ ε → ℂ) (Ω : Set (Formalism.REAL.UJ ε)) (a : ℝ), IsCompact Ω ∧
      Measurable α ∧ (∀ g, α g ≠ 0 → g ∈ Ω) ∧ (∀ g, ‖α g‖ ≤ a) ∧
      Integrable (fun g => α g • σ (uMat g) w) (Formalism.REAL.muG ε) ∧
      ∫ g, α g • σ (uMat g) w ∂(Formalism.REAL.muG ε) = w

section KFin

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem finsetSup_kstable (s : Finset (Submodule ℂ H))
    (hs : ∀ S ∈ s, FiniteDimensional ℂ S ∧ IsKStableOn ε σ S) :
    FiniteDimensional ℂ ↥(s.sup (id : Submodule ℂ H → Submodule ℂ H)) ∧
      IsKStableOn ε σ (s.sup (id : Submodule ℂ H → Submodule ℂ H)) := by
  refine Finset.sup_induction
    (p := fun S : Submodule ℂ H => FiniteDimensional ℂ S ∧ IsKStableOn ε σ S) ?_ ?_ hs
  · refine ⟨inferInstance, ?_⟩
    unfold IsKStableOn
    intro g _ v hv
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]
    exact zero_mem _
  · rintro S₁ ⟨hfd1, hst1⟩ S₂ ⟨hfd2, hst2⟩
    have := hfd1
    have := hfd2
    refine ⟨inferInstance, ?_⟩
    unfold IsKStableOn at hst1 hst2 ⊢
    intro g hg v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hst1 g hg y hy) (hst2 g hg z hz)

theorem isKFin_of_mem_lowKSub {lam : Fin n → ℝ} {w : H} (hw : w ∈ lowKSub ε lam σ) : IsKFin ε σ w := by
  unfold IsKFin lowKSub at *
  unfold IsKTypeOf at hw
  obtain ⟨s, hs, hws⟩ := (Submodule.mem_sSup_iff_exists_finset).1 hw
  obtain ⟨hfd, hst⟩ := finsetSup_kstable s (fun S hS => ⟨(hs hS).1, (hs hS).2.1⟩)
  exact ⟨_, hfd, by simpa [Finset.sup_eq_iSup] using hws, hst⟩

end KFin

theorem hcReprodDSc : HCReprodDSc := by
  intro n ε lam H _ _ _ σ hDS w hw
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hirr : IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  have hadm : AdmProjAt ε σ := _root_.Formalism.L2.SG.Pf.admitted.hcAdmDS n ε lam H σ hDS
  by_cases h0 : w = 0
  · exact ⟨0, continuous_const, HasCompactSupport.zero, by simp, by simp [h0]⟩
  · obtain ⟨Φ, hΦ, hx⟩ := kfin_mem_Vsub hσ hirr hadm h0 (isKFin_of_mem_lowKSub hw)
    exact ⟨fun y => Φ (umat y), hΦ.1.continuous.comp continuous_umat, test_comp_cs hΦ,
      vec_integrable hσ w hΦ, hx.symm⟩

theorem hcReprodDSm : HCReprodDSm := by
  intro n ε lam H _ _ _ σ hds w hw
  obtain ⟨α, hc, hcs, hi, he⟩ := hcReprodDSc n ε lam H σ hds w hw
  obtain ⟨a, ha⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨α, tsupport α, a, hcs.isCompact, hc.measurable, fun g hg => subset_tsupport α hg, ha, hi, he⟩

end Formalism.L2.SG.HCReprodM
