module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosPartProjIndep
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSumMeasurable
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

namespace PtsPosDens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_ofWeight_one {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    logNorm (HermLine.ofWeight g hg.2) 1 = g := by
  funext z
  simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]

theorem isSmoothHerm_ofWeight {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSmoothHerm (HermLine.ofWeight g hg.2) :=
  show ContDiffOn ℝ _ (fun z => Real.exp (-g z)) _ from Real.contDiff_exp.comp_contDiffOn hg.1.neg

theorem isSectionOn_ofWeight_one {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSectionOn P (HermLine.ofWeight g hg.2) 1 := by
  refine ⟨0, fun k => by simp [HermLine.ofWeight], fun m hm k => ?_,
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem exists_bound {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    ∃ M : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → |g z| ≤ M := by
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = 1} with hTdef
  have hTc : IsClosed T := by
    rw [hTdef, Set.ofPred_forall]
    exact isClosed_iInter fun k =>
      isClosed_eq (continuous_norm.comp (continuous_pi fun i => continuous_apply _)) continuous_const
  have hTb : T ⊆ Metric.closedBall 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    have h1 := norm_le_pi_norm (fun i : ι p.1 => z ⟨p.1, i⟩) p.2
    rw [hz p.1] at h1
    exact h1
  have hTK : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTc (Metric.isBounded_closedBall.subset hTb)
  have hTU : T ⊆ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    push Not at h
    have h0 : (fun i : ι k => z ⟨k, i⟩) = 0 := funext h
    have := hz k
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨M, hM⟩ := hTK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hTU)
  refine ⟨M, fun z hz => ?_⟩
  have hb : ∀ k, (fun i : ι k => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  set c : K → ℂ := fun k => ((‖fun i : ι k => z ⟨k, i⟩‖ : ℝ) : ℂ)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k =>
    inv_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hb k)))
  have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ T := by
    intro k
    have : (fun i : ι k => c k * z ⟨k, i⟩) = c k • fun i : ι k => z ⟨k, i⟩ := rfl
    rw [this, norm_smul, hcdef]
    simp only [norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hb k))
  rw [← hg.2 c z hc]
  exact hM _ hmem

theorem isSemiPosHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAp : Inter.IsSemiPosHerm A) (hBp : Inter.IsSemiPosHerm B) : Inter.IsSemiPosHerm (A.tensor B) := by
  intro z hz v
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := isOpen_blockNonzero
  have hline : Continuous fun t : ℂ => z + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    refine hline.continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hz
  have hsm : ∀ C : HermLine ι, IsSmoothHerm C →
      ContDiffAt ℝ 2 (fun t : ℂ => Real.log (C.h (z + t • v))) 0 := by
    intro C hC
    have h1 : ContDiffAt ℝ 2 C.h (z + (0 : ℂ) • v) := by
      rw [zero_smul, add_zero]
      exact (hC.contDiffAt (hU.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)
    have h2 : ContDiffAt ℝ 2 (fun t : ℂ => z + t • v) 0 := by fun_prop
    have h3 := h1.comp (0 : ℂ) h2
    refine h3.log ?_
    simp only [Function.comp, zero_smul, add_zero]
    exact (C.pos z hz).ne'
  have heq : (fun t : ℂ => Real.log ((A.tensor B).h (z + t • v))) =ᶠ[𝓝 0]
      (fun t : ℂ => Real.log (A.h (z + t • v))) + fun t : ℂ => Real.log (B.h (z + t • v)) := by
    filter_upwards [hev] with t ht
    simp only [Pi.add_apply, HermLine.tensor]
    exact Real.log_mul (A.pos _ ht).ne' (B.pos _ ht).ne'
  rw [(laplacian_congr_nhds heq).eq_of_nhds, (hsm A hA).laplacian_add (hsm B hB)]
  exact add_nonneg (hAp z hz v) (hBp z hz v)

theorem aestronglyMeasurable {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) :
    AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) := by
  classical
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (isSmoothHerm_ofWeight hg) (isSectionOn_ofWeight_one hP hg)
  rw [logNorm_ofWeight_one hg] at hind
  exact PtsSumMeasurable.aestronglyMeasurable_finsum (g := g) (φ := (max · 0))
    hP hΨ (measurable_id.max measurable_const) (max_self 0)
    (fun B γ hBo hγc hO => ⟨B.piecewise (fun y => g (γ y)) 0,
      (hg.1.continuousOn.comp hγc hO).measurable_piecewise continuousOn_const hBo.measurableSet,
      fun y hy => Set.piecewise_eq_of_mem _ _ _ hy⟩)
    hind

end PtsPosDens

end GroundTheory.Heights₂.Heights
