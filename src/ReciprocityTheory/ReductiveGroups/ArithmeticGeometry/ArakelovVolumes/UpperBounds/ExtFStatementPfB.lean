module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_dmin (τ : X.Ψ) (i : Fin (r + 1)) : Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor gram hermC col mat
  first
    | fun_prop

theorem nfac_contOn (la : Wt X.Ψ r) : ContinuousOn (X.nfac la) X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => cont_dmin X τ i
  have hne : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro x hx τ i h0
    have h1 := (hx τ).2 i
    rw [h0] at h1
    simp at h1
  unfold Data.nfac
  apply continuousOn_finsetProd
  intro τ _
  apply continuousOn_finsetProd
  intro i _
  apply ContinuousOn.rpow_const
  · exact (((hd τ i.succ).continuousOn).div ((hd τ i.castSucc).continuousOn)
      (fun x hx => hne x hx τ i.castSucc)).norm
  · intro x hx
    left
    exact norm_ne_zero_iff.2 (div_ne_zero (hne x hx τ i.succ) (hne x hx τ i.castSucc))

variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)

def Gf (x : Frame X.Ψ r) : ℝ≥0∞ := ENNReal.ofReal (X.pnorm la (P0 D la F) x ^ 2)

private lemma dom_isOpen : IsOpen X.dom := by
  apply _root_.ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom <;> assumption

private lemma continuous_cpt' : Continuous (cpt X x0) := by
  have hn : ∀ (τ : X.Ψ) (a b : Fin r), Continuous fun z : V (nd X) => nmat X z τ a b := by
    intro τ a b
    by_cases h : b < a
    · simp only [nmat, dite_eq_left h]
      first
        | exact (EuclideanSpace.proj (𝕜 := ℂ) _).continuous
    · by_cases h' : a = b
      · simp only [nmat, dite_eq_right h, ite_eq_left h']
        exact continuous_const
      · simp only [nmat, dite_eq_right h, ite_eq_right h']
        exact continuous_const
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun z => ∑ k, mat x0 τ a k * mat (nmat X z) τ k b
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hn τ k b)

theorem Gf_meas (hF : DifferentiableOn ℂ F (OmF X x0)) : Measurable (Gf D la F) := by
  classical
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => cont_dmin X τ i
  have hfc : ContinuousOn (fun x => bchar la (D.bOf x) * F (D.zOf x)) (cell D) := by
    have hzc : ContinuousOn D.zOf (cell D) := D.hz.continuousOn
    have hbc : ContinuousOn D.bOf (cell D) := D.hb.continuousOn
    have hsplit : ∀ x ∈ cell D, D.zOf x ∈ OmF X x0 ∧ D.bOf x ∈ Bor X.Ψ r :=
      fun x hx => ⟨(D.split x hx.1 hx.2).1, (D.split x hx.1 hx.2).2.1⟩
    refine ContinuousOn.mul ?_ (hF.continuousOn.comp hzc fun x hx => (hsplit x hx).1)
    unfold bchar
    apply continuousOn_finsetProd
    intro τ _
    apply continuousOn_finsetProd
    intro i _
    apply ContinuousOn.zpow₀
    · have hent : Continuous fun y : Frame X.Ψ r => y τ i i := by
        first
          | fun_prop
      exact hent.comp_continuousOn hbc
    · intro x hx
      left
      exact FrameDegreeData.bdiag_ne X (hsplit x hx).2 τ i
  have hP : P0 D la F = (cell D).piecewise (fun x => bchar la (D.bOf x) * F (D.zOf x)) 0 := by
    funext x
    by_cases h : x ∈ cell D
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact ite_eq_left h
    · first
        | rw [Set.piecewise_eq_of_notMem _ _ _ h]
      exact ite_eq_right h
  have hPm : Measurable (P0 D la F) := by
    rw [hP]
    exact hfc.measurable_piecewise continuous_zero.continuousOn (isOpen_cell D).measurableSet
  have hnf : Measurable fun x => X.nfac la x := by
    unfold Data.nfac
    apply Finset.measurable_prod
    intro τ _
    apply Finset.measurable_prod
    intro i _
    exact (((hd τ i.succ).measurable.div (hd τ i.castSucc).measurable).norm).pow_const _
  have hp : ∀ x, X.pnorm la (P0 D la F) x = ‖P0 D la F x‖ * X.nfac la x := fun x => rfl
  unfold Gf
  simp only [hp]
  first
    | exact ((hPm.norm.mul hnf).pow_const 2).ennreal_ofReal

theorem Gf_inv {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    Gf D la F (rmul x b) = Gf D la F x := by
  unfold Gf
  rw [FrameDegreeData.pnorm_rmul X la _ (fun y hy b' hb' => poincareLift_borel_equivariant D la F hy hb') x hx b hb]

theorem Gf_cpt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Gf D la F (cpt X x0 z) = ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) := by
  have hpos := FlowCoefficientBounds.nfac_pos X hz la
  unfold Gf
  have hp : X.pnorm la (P0 D la F) (cpt X x0 z) =
      ‖P0 D la F (cpt X x0 z)‖ * X.nfac la (cpt X x0 z) := rfl
  rw [hp, poincareLift_on_chart D la F hz]
  congr 1
  unfold phla
  have hl : -(-2 * Real.log (X.nfac la (cpt X x0 z))) = Real.log (X.nfac la (cpt X x0 z) ^ 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hl, Real.exp_log (pow_pos hpos 2), mul_pow]

theorem norm_poincareLift_sq_le {x : Frame X.Ψ r} (_hx : x ∈ X.dom) {m : ℝ} (hm : 0 < m) (hmx : m ≤ X.nfac la x) :
    ENNReal.ofReal (‖P0 D la F x‖ ^ 2) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * Gf D la F x := by
  unfold Gf
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg m))]
  apply ENNReal.ofReal_le_ofReal
  have hp : X.pnorm la (P0 D la F) x = ‖P0 D la F x‖ * X.nfac la x := rfl
  rw [hp]
  have hm2 : 0 < m ^ 2 := by positivity
  have h1 : m ^ 2 ≤ X.nfac la x ^ 2 := by
    have := hm.le
    gcongr
  have h2 : 1 ≤ (m ^ 2)⁻¹ * X.nfac la x ^ 2 := by
    rw [inv_mul_eq_div, one_le_div hm2]
    exact h1
  rw [mul_pow, ← mul_assoc, mul_comm ((m ^ 2)⁻¹), mul_assoc]
  exact le_mul_of_one_le_right (sq_nonneg _) h2

theorem ae_OmF : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
  have hmeas : MeasurableSet (OmF X x0) :=
    (dom_isOpen.preimage continuous_cpt').measurableSet
  unfold muF
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hmeas)

theorem poincareLift_locally_squareIntegrable (hM : FrameMeasStatement (E := E)) (hx0 : IsOrth X x0)
    (hF : DifferentiableOn ℂ F (OmF X x0))
    (hL2 : ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤)
    {C : Set (Frame X.Ψ r)} (hC : IsCompact C) (hCd : C ⊆ X.dom) :
    ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2) < ⊤ := by
  obtain ⟨K, hK, hKG⟩ := hM r X x0 hx0 C hC hCd
  obtain ⟨m, hm, hmC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ C, m ≤ X.nfac la x := by
    rcases C.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨x1, hx1, hmin⟩ := hC.exists_isMinOn h ((nfac_contOn X la).mono hCd)
    exact ⟨X.nfac la x1, FlowCoefficientBounds.nfac_pos X (hCd hx1) la, fun x hx => hmin hx⟩
  have h1 : ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2) ≤
      ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ x in C, Gf D la F x := by
    rw [← lintegral_const_mul _ (Gf_meas D la F hF)]
    exact setLIntegral_mono' hC.measurableSet fun x hx => norm_poincareLift_sq_le D la F (hCd hx) hm (hmC x hx)
  have h2 := hKG (Gf D la F) (Gf_meas D la F hF) fun x hx b hb => Gf_inv D la F hx hb
  have h3 : ∫⁻ z in sat X x0 C, Gf D la F (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_OmF (x0 := x0))] with z hz
    rw [Gf_cpt D la F hz]
  calc ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2)
      ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * (K * ∫⁻ z in sat X x0 C,
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0) :=
        h1.trans (mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl h3)))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hK (hL2 C hC hCd))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
