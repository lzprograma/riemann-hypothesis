module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace

@[expose] public section

noncomputable section

open Matrix MeasureTheory Topology
open scoped ComplexConjugate ENNReal NNReal

namespace WlocSk.HM

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

abbrev Hb (k : ℕ) := Formalism.QuantumDeterminants.Hb k
abbrev embWb (k r : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := Formalism.FourierDecayAlt.B2.embWb k r μ
abbrev UWb (k r : ℕ) := Formalism.FourierDecayAlt.B2.UWb k r

theorem hpk_herm : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

theorem uw_clsub (z : Fin (2 * r + k + 1) → ℂ) : ClSub (UWset k r z : Set (Mx k r)) := by
  refine ⟨⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, ?_, ?_,
    fun a ha => isUnit_of_uh ha.1, ?_⟩
  · intro a ha b hb
    refine ⟨uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
    · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
    · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]
  · intro a ha
    have hu := isUnit_of_uh ha.1
    have fix : ∀ v, a *ᵥ v = v → a⁻¹ *ᵥ v = v := by
      intro v hv
      calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [hv]
        _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    exact ⟨uh_inv ha.1, fun c => ⟨fix _ (ha.2.1 c).1, fix _ (ha.2.1 c).2⟩, fix _ ha.2.2⟩
  · have hv : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {g : Mx k r | g *ᵥ v = v} := fun v =>
      isClosed_eq (Continuous.matrix_mulVec continuous_id continuous_const) continuous_const
    have e : (UWset k r z : Set (Mx k r)) = UH (Hpk k r) ∩
        ((⋂ a : Fin r, ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g : Mx k r | g *ᵥ z = z}) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      exact Iff.rfl
    rw [e]
    exact uh_closed.inter ((isClosed_iInter fun a => (hv _).inter (hv _)).inter (hv z))

abbrev midx {i : Fin (2 * r + k + 1)} (hi : Formalism.FourierDecayAlt.P.B2x3.mid k r i) : Fin (k + 1) :=
  Formalism.FourierDecayAlt.P.B2x3.midx hi

alias wI_midx := Formalism.FourierDecayAlt.P.B2x3.wI_midx
alias emb_out_col := Formalism.FourierDecayAlt.P.B2x3.emb_out_col
alias emb_out_row := Formalism.FourierDecayAlt.P.B2x3.emb_out_row
alias emb_mid := Formalism.FourierDecayAlt.P.B2x3.emb_mid
alias Em_mul_mid := Formalism.FourierDecayAlt.P.B2x3.Em_mul_mid
alias mul_EmT_mid := Formalism.FourierDecayAlt.P.B2x3.mul_EmT_mid
alias emb_eq := Formalism.FourierDecayAlt.P.B2x3.emb_eq
alias Hpk_Em := Formalism.FourierDecayAlt.P.B2x3.Hpk_Em
alias sandwich := Formalism.FourierDecayAlt.P.B2x3.sandwich
alias emb_one := Formalism.FourierDecayAlt.P.B2x3.emb_one
alias emb_conjT := Formalism.FourierDecayAlt.P.B2x3.emb_conjT
alias Hb_conjT := Formalism.FourierDecayAlt.P.B2x3.Hb_conjT
alias EmT_Hpk := Formalism.FourierDecayAlt.P.B2x3.EmT_Hpk
alias emb_form := Formalism.FourierDecayAlt.P.B2x3.emb_form
alias Hpk_eq := Formalism.FourierDecayAlt.P.B2x3.Hpk_eq
alias emb_mem := Formalism.FourierDecayAlt.P.B2x3.emb_mem
alias emb_linv := Formalism.FourierDecayAlt.P.B2x3.emb_linv
alias fix_dual := Formalism.FourierDecayAlt.P.B2x3.fix_dual
alias uwb_col := Formalism.FourierDecayAlt.P.B2x3.uwb_col
alias uwb_row := Formalism.FourierDecayAlt.P.B2x3.uwb_row
alias uwb_eq_emb := Formalism.FourierDecayAlt.P.B2x3.uwb_eq_emb
alias emb_fix := Formalism.FourierDecayAlt.P.B2x3.emb_fix
alias uwb_iff := Formalism.FourierDecayAlt.P.B2x3.uwb_iff
alias emb_cont := Formalism.FourierDecayAlt.P.B2x3.emb_cont
alias hb_form := Formalism.FourierDecayAlt.P.B2x3.hb_form
alias hb_self_re := Formalism.FourierDecayAlt.P.B2x3.hb_self_re
alias col_bound := Formalism.FourierDecayAlt.P.B2x3.col_bound
alias herm_wb := Formalism.FourierDecayAlt.P.B2x3.herm_wb
theorem compactW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (ht : 0 < Tz k r z) :
    IsCompact (UWset k r z : Set (Mx k r)) :=
  Formalism.FourierDecayAlt.P.B2x3.compactW k r z hz ht

end WlocSk.HM
