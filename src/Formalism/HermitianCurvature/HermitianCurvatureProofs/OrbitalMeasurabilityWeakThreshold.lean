module

public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordIntegralScaling
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.WeakThresholdClauses

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

open scoped Matrix.Norms.Elementwise

def WeakDominationThreshold (k r : ℕ) (A : ℝ) (m : ℕ) : Prop :=
  0 < A - 6 * (r : ℝ) * (m : ℝ) ∧
    (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1) < A - 6 * (r : ℝ) * (m : ℝ)

def NNMajW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    WeakDominationThreshold k r A m →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * B.gN (B.sgs p g) ^ (-A) ≤ b p

def JDomBoundW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    WeakDominationThreshold k r A m → B.InCC A m F →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JDomMeasW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    WeakDominationThreshold k r A m → B.InCC A m F →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS

def JWordsW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    WeakDominationThreshold k r A m → B.InCC A m F →
    Q.CkLev k r 0 m (Q.OmPlus k r D.z D.z') (B.JF D F) ∧
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        Integrable (fun p => xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS ∧
        B.dLR u v (B.JF D F) g =
          ∫ p, xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g ∂D.μSS

end Formalism.FourierDecayAlt.P.WeakThresholdClauses

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism.FourierDecayAlt.P.WeakDominationMajorants

open scoped Matrix.Norms.Elementwise

theorem scalar_majorant_weak_threshold : Formalism.FourierDecayAlt.P.WeakThresholdClauses.NNMajW := by
  intro k r Wp Wq _ _ _ _ D A m hThr K hK hKO
  have hthr : r = 0 ∨ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) <
      (A - 6 * (r : ℝ) * (m : ℝ)) / (6 * (r : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact Or.inl h
    · right
      rw [lt_div_iff₀ (by positivity)]
      exact hThr.2
  exact nnMaj_core k r Wp Wq D A m hThr.1 hthr K hK hKO

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

namespace Formalism.FourierDecayAlt.P.JFxDs2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

open scoped Matrix.Norms.Elementwise

theorem domination_of_scalar_majorant : Formalism.FourierDecayAlt.P.WeakThresholdClauses.NNMajW → Formalism.FourierDecayAlt.P.WeakThresholdClauses.JDomBoundW := by
  intro hN k r Wp Wq _ _ _ _ _ _ D A m F hThr hF K hK hKO
  obtain ⟨c, hc⟩ := hF
  have hc0 : 0 ≤ c := B4.cc_nonneg hc
  obtain ⟨b, hb, hbd⟩ := hN k r Wp Wq D A m hThr K hK hKO
  refine ⟨fun p => c * b p, hb.const_mul c, fun u v hu hv hl g hg => ?_⟩
  filter_upwards [hbd u v hu hv hl g hg, B5.ae_inSS D] with p hp hSS
  have hgG : g ∈ GV k r := (hKO hg).1
  have hx : sgs p g ∈ GV k r := B7.sgs_mem D hSS hgG
  have hpos : 0 < gN (sgs p g) := B6.gN_pos hx
  have hw := allLie_ad (sL_mem hSS) (sR_mem hSS) hu hv
  have hB := B4.bound_scaled hc (B4.lr (u.map (AdL p)) (v.map (AdR p))) (B4.lrt_lr _ _) hw
    (by rw [B4.length_lr]; simpa using hl) _ hx
  rw [← B4.dLR_eq, pn_lr] at hB
  have hApos : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hpos A
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      c * ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * gN (sgs p g) ^ (-A)) := by
    rw [Real.rpow_neg hpos.le]
    rw [mul_comm (gN (sgs p g) ^ A) _, ← le_div_iff₀ hApos] at hB
    calc _ ≤ _ := hB
      _ = _ := by rw [div_eq_mul_inv]; ring
  calc ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖
      ≤ ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ := B7.norm_rho_le D hSS _ g
    _ ≤ _ := h1
    _ ≤ c * b p := mul_le_mul_of_nonneg_left hp hc0

end Formalism.FourierDecayAlt.P.JFxDs2

namespace Formalism.FourierDecayAlt.P.JFxDs3

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

open scoped Matrix.Norms.Elementwise

variable {k r : ℕ}

theorem orbital_measurability_weak_threshold : Formalism.FourierDecayAlt.P.WeakThresholdClauses.JDomMeasW := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hF u v hu hv hl g hg
  obtain ⟨c, hc⟩ := hF
  have hgG : g ∈ GV k r := hg.1
  have hA : 0 ≤ A := by
    have h1 := hThr.1
    have h2 : (0 : ℝ) ≤ 6 * (r : ℝ) * (m : ℝ) := by positivity
    linarith
  have hΦ := continuousOn_rho_dLR D hc hA u v hu hv hl hgG
  have := hΦ.aestronglyMeasurable (μ := D.μSS) (B6.measurableSet_inSS D)
  have hr : D.μSS.restrict {p | D.inSS p} = D.μSS := Measure.restrict_eq_self_of_ae_mem (B5.ae_inSS D)
  rwa [hr] at this

end Formalism.FourierDecayAlt.P.JFxDs3

namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion

open scoped Matrix.Norms.Elementwise

theorem orbital_derivative_words_weak : Formalism.FourierDecayAlt.P.WeakThresholdClauses.JWordsW := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  have hDom1 := Formalism.FourierDecayAlt.P.JFxDs3.orbital_measurability_weak_threshold k r Wp Wq D A m F hThr hCC
  have hDom2 := Formalism.FourierDecayAlt.P.JFxDs2.domination_of_scalar_majorant Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.scalar_majorant_weak_threshold k r Wp Wq D A m F hThr hCC
  obtain ⟨c, hc⟩ := hCC
  have hFm : CkOn (m : ℕ∞) (GV k r) F := hc.1
  have hW := words_all D hFm hDom1 hDom2
  refine ⟨ck_all D hFm hDom1 hDom2, fun u v hu hv hl g hg => ?_⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  have hb := hbd u v hu hv hl g (Set.mem_singleton g)
  refine ⟨hbdI.norm.mono' ((continuous_xiP D).aestronglyMeasurable.smul (hDom1 u v hu hv hl g hg)) ?_, ?_⟩
  · filter_upwards [hb] with p hp
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_xiP D p)).trans (hp.trans (Real.le_norm_self _))
  · rw [hW u v hu hv hl g hg]
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp
    rw [dLR_rho D hp]

end Formalism.FourierDecayAlt.P.WeakDominationWordBounds

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

open scoped Matrix.Norms.Elementwise

theorem orbital_commutes_on_open_set : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)) (Θ : DiffOp k r Wp Wq)
    (UU : Set (Mat k r)), UU ⊆ Om k r D.z D.z' → opOrder Θ ≤ m → Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A m → InCC A m F →
    Commutes D UU Θ → ∀ g ∈ UU, opApply Θ (JF D F) g = JF D (opApply Θ F) g := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F Θ UU hUU ho hT hF hC g hgU
  have hg : g ∈ Om k r D.z D.z' := hUU hgU
  have hW := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak
  have hR := Formalism.FourierDecayAlt.P.rewrite_rho_action
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hCo : CkOn (opOrder Θ : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast ho) hCk
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp F hCo g hgU]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

end Formalism.FourierDecayAlt.P
