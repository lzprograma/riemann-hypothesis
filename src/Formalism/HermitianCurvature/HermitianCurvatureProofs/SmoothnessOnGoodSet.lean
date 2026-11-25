module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.StatementJF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartIntegralLocal

@[expose] public section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ∞) :
    CkOn m (GV k r) (fun _ : Mat k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma dLR_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : List (Mat k r)) :
    dLR u v (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
  have hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show RdV X (Rw w _) = _
      rw [ih]
      funext g
      simp only [RdV, deriv_const']
  induction u with
  | nil => exact hR v
  | cons X u ih =>
    show LdV X (dLR u v _) = _
    rw [ih]
    funext g
    simp only [LdV, deriv_const']

lemma norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [Complex.norm_exp]
  simp

lemma isOpen_OmPlus (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Formalism.FourierDecayAlt.Q.OmPlus k r z z') := by
  apply _root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open <;> assumption

lemma cv_continuous (b : Bool) (X g : Mat k r) : Continuous fun t : ℝ => cv b X t g := by
  cases b
  · exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  · have h := (Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous
    have h2 := (continuous_mul_const g).comp h
    refine h2.congr fun t => ?_
    simp [cv, smul_neg]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma norm_xiP (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiP D p‖ ≤ 1 := by
  unfold xiP
  simp [norm_psi]

lemma continuous_xiP (D : RealPlaceData k r Wp Wq) : Continuous (xiP D) := by
  have key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M) := by
    intro z
    unfold ell
    refine continuous_finsetSum _ fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, ↓reduceDIte, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]
      refine continuous_finsetSum _ fun j _ => ?_
      first
        | fun_prop
  have hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M) := by
    intro z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (key z)))))
  unfold xiP
  exact ((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul
    (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))

lemma ckOn_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) :=
  by apply _root_.Formalism.FourierDecayAlt.P.B5.ckOn_rho <;> assumption

lemma ckOn_dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X)
    (hv : ∀ X ∈ v, unitLie k r X) (j : ℕ) (hl : j + (u.length + v.length) ≤ m) :
    CkOn ((j : ℕ) : ℕ∞) (GV k r) (dLR u v (rho D p F)) := by
  rw [dLR_eq]
  exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) j (ckOn_mono (by rw [length_lr]; omega) (ckOn_rho D hp hF))

lemma good_set (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F)
    {K : Set (Mat k r)} (hK : IsCompact K) (hKG : K ⊆ GV k r)
    {WS : Set (List (Mat k r) × List (Mat k r))} (hWS : WS.Countable)
    (hWSl : ∀ uv ∈ WS, (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m)
    (b : SS k r → ℝ)
    (hb : ∀ uv ∈ WS, ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖rho D p (dLR (uv.1.map (AdL p)) (uv.2.map (AdR p)) F) g‖ ≤ b p) :
    ∀ᵐ p ∂D.μSS, D.inSS p ∧ ∀ uv ∈ WS, ∀ g ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g‖ ≤ b p := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat k r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨S, hSK, hSc, hKS⟩ := hK.isSeparable.exists_countable_dense_subset
  haveI := hWS.to_subtype
  haveI := hSc.to_subtype
  have hall : ∀ᵐ p ∂D.μSS, ∀ i : WS × S,
      ‖rho D p (dLR (i.1.1.1.map (AdL p)) (i.1.1.2.map (AdR p)) F) i.2.1‖ ≤ b p :=
    ae_all_iff.2 fun i => hb i.1.1 i.1.2 i.2.1 (hSK i.2.2)
  filter_upwards [hall, Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp hpS
  refine ⟨hpS, fun uv huv g hg => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hWSl uv huv
  have hcont : ContinuousOn (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) (GV k r) :=
    (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_dLR_rho D hpS hF h1 h2 0 (by omega))).norm
  have hcl : IsClosed (GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p)) :=
    hcont.preimage_isClosed_of_isClosed Formalism.FourierDecayAlt.P.B5.GV_closed isClosed_Iic
  have hS : S ⊆ GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p) := by
    intro x hx
    refine ⟨hKG (hSK hx), ?_⟩
    show ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ b p
    rw [dLR_rho D hpS]
    exact hp ⟨⟨uv, huv⟩, ⟨x, hx⟩⟩
  exact (hcl.closure_subset_iff.2 hS (hKS hg)).2

lemma curve_ball (D : RealPlaceData k r Wp Wq) {g : Mat k r} (hg : g ∈ Om k r D.z D.z') (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ Om k r D.z D.z' := by
  have hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') :=
    (isOpen_OmPlus _ _).preimage (cv_continuous b X g)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := by
    show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'
    rw [cv_zero]; exact hg.2
  obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := hg
  refine ⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩
  rw [Metric.mem_closedBall] at ht
  rw [Metric.mem_ball]
  linarith

end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
