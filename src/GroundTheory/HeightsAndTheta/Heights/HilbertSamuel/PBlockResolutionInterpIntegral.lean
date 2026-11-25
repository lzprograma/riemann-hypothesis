module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionInterpIntegral
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionInterpIntegral

variable {D : ℕ} {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)}

theorem locDens_interp (R : AnRes P J D) {A₀ A₁ : HermLine ι} (hA₀ : IsSmoothHerm A₀)
    (hA₁ : IsSmoothHerm A₁) (t : ℝ) {Φ : LocPot R.X}
    (hΦ : ∀ x y, y ∈ R.U x → Φ.φ x y = (1 - t) * Real.log (A₀.h (R.lift x y)) + t * Real.log (A₁.h (R.lift x y)))
    (j : Fin R.A.n) {y : Fin D → ℂ} (hy : y ∈ (R.A.chart j).target) :
    locDens R.A (fun _ => Φ) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf R A₁
          else AnResBridge.potOf R A₀) j y := by
  set x0 := (R.A.chart j).symm y with hx0
  set a : (Fin D → ℂ) → ℝ := fun y' => Real.log (A₀.h (R.lift x0 ((R.A.chart j).symm y'))) with ha
  set b : (Fin D → ℂ) → ℝ := fun y' => Real.log (A₁.h (R.lift x0 ((R.A.chart j).symm y'))) with hb
  have hV : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hyV : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 := ⟨hy, R.mem_U x0⟩
  have hsm : ∀ {L : HermLine ι}, IsSmoothHerm L → ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ 2 (fun y'' => Real.log (L.h (R.lift x0 ((R.A.chart j).symm y'')))) y' := by
    intro L hL
    filter_upwards [hV.mem_nhds hyV] with y' hy'
    exact_mod_cast contDiffAt_infty.mp
      ((AnResBridge.contDiffOn_potOf R hL x0 j).contDiffAt (hV.mem_nhds hy')) 2
  have hH := gaamix_cxHessian_comb (ψ := fun y' => Φ.φ x0 ((R.A.chart j).symm y')) (1 - t) t
    (hsm hA₀) (hsm hA₁) (by filter_upwards [hV.mem_nhds hyV] with y' hy'; exact hΦ x0 ((R.A.chart j).symm y') hy'.2)
  set H₀ := cxHessian a y
  set H₁ := cxHessian b y
  have hL : locDens R.A (fun _ => Φ) j y =
      ReciprocityTheory.AnForm.maDens (fun _ y' => Φ.φ x0 ((R.A.chart j).symm y')) y := rfl
  have hR : ∀ i, locDens R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf R A₁
      else AnResBridge.potOf R A₀) j y =
      ReciprocityTheory.AnForm.maDens (fun k => if k.val < i then b else a) y := by
    intro i
    show ReciprocityTheory.AnForm.maDens _ y = _
    congr 1
    funext k y'
    by_cases hk : k.val < i
    · simp only [hk, ite_true]; rfl
    · simp only [hk, ite_false]; rfl
  have hpure : (fun _ : Fin D => ReciprocityTheory.AnForm.hessC (fun y' => Φ.φ x0 ((R.A.chart j).symm y')) y) =
      fun _ => (t : ℂ) • H₁ + (1 - (t : ℂ)) • H₀ := by
    funext k
    show cxHessian _ y = _
    rw [hH, add_comm]
    push_cast
    rfl
  have hmix : ∀ i, (fun k : Fin D => ReciprocityTheory.AnForm.hessC (if k.val < i then b else a) y) =
      fun k : Fin D => if k.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [hk, ite_true]; rfl
    · simp only [hk, ite_false]; rfl
  rw [hL]
  simp only [hR]
  unfold ReciprocityTheory.AnForm.maDens
  rw [hpure, ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem continuous_logRatio (R : AnRes P J D) {A₀ A₁ : HermLine ι} (hdeg : A₁.a = A₀.a)
    (hA₀ : IsSmoothHerm A₀) (hA₁ : IsSmoothHerm A₁) :
    Continuous fun x => Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x)) := by
  have hE : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
      ext z; simp
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hΦ : ContinuousOn (fun z : (Σ k, ι k) → ℂ => Real.log (A₁.h z / A₀.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA₁.continuousOn.div hA₀.continuousOn fun z hz => (A₀.pos z hz).ne').log fun z hz =>
      (div_pos (A₁.pos z hz) (A₀.pos z hz)).ne'
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
  have hl : ContinuousAt (R.lift x₀) x₀ :=
    (continuousOn_pi.2 fun p => AnResBridge.continuousOn_lift R x₀ p).continuousAt hU
  have h0 : R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (R.mem x₀ x₀ (R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Real.log (A₁.h (R.lift x₀ x) / A₀.h (R.lift x₀ x))) x₀ :=
    (hΦ.continuousAt (hE.mem_nhds h0)).comp hl
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := R.compat x x₀ x ⟨R.mem_U x, hx⟩
  show _ = Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x))
  have hp : (∏ k, ‖c k‖ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc0 k))
  rw [he, A₁.smul c _ hc0, A₀.smul c _ hc0, hdeg, mul_div_mul_left _ _ hp]

theorem mInt_interp (R : AnRes P J D) {A₀ A₁ : HermLine ι} (hdeg : A₁.a = A₀.a)
    (hA₀ : IsSmoothHerm A₀) (hA₁ : IsSmoothHerm A₁) (t : ℝ) {Φ : LocPot R.X}
    (hΦ : ∀ x y, y ∈ R.U x → Φ.φ x y = (1 - t) * Real.log (A₀.h (R.lift x y)) + t * Real.log (A₁.h (R.lift x y))) :
    mInt R.A (fun _ => Φ) (fun x => Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x))) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf R A₁
            else AnResBridge.potOf R A₀)
          (fun x => Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x))) := by
  have hg := continuous_logRatio R hdeg hA₀ hA₁
  have hPot : ∀ (i : ℕ) (k : Fin D), IsPotential R.A
      (if k.val < i then AnResBridge.potOf R A₁ else AnResBridge.potOf R A₀) := by
    intro i k
    split_ifs
    · exact AnResBridge.isPotential_potOf R hA₁
    · exact AnResBridge.isPotential_potOf R hA₀
  unfold mInt
  by_cases hP : Nonempty (ChartPartition R.A)
  · simp only [dite_eq_left hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((R.A.chart j).symm y) *
            Real.log (A₁.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) /
              A₀.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y))) *
            locDens R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf R A₁
              else AnResBridge.potOf R A₀) j y))
        (volume.restrict (R.A.chart j).target) := fun i _ =>
      (integrableOn_weight R.A hP.some _ _ (mIntegrableCont R.A _ (hPot i) _ hg) j).const_mul _
    calc _ = ∫ y in (R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((R.A.chart j).symm y) *
              Real.log (A₁.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) /
                A₀.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y))) *
              locDens R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf R A₁
                else AnResBridge.potOf R A₀) j y) := by
          refine setIntegral_congr_fun (R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_interp R hA₀ hA₁ t hΦ j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dite_eq_right hP, mul_zero, Finset.sum_const_zero]

theorem interp_integral_eq (R : AnRes P J D) {A₀ A₁ : HermLine ι} (hdeg : A₁.a = A₀.a)
    (hA₀ : IsSmoothHerm A₀) (hA₁ : IsSmoothHerm A₁) (Φ : ℝ → LocPot R.X)
    (hΦ : ∀ t x y, y ∈ R.U x → (Φ t).φ x y = (1 - t) * Real.log (A₀.h (R.lift x y)) + t * Real.log (A₁.h (R.lift x y))) :
    ((D : ℝ) + 1) * (∫ t in (0 : ℝ)..1, mInt R.A (fun _ => Φ t)
        (fun x => Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x)))) =
      ∑ i ∈ Finset.range (D + 1),
        mInt R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf R A₁
            else AnResBridge.potOf R A₀)
          (fun x => Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x))) := by
  simp only [mInt_interp R hdeg hA₀ hA₁ _ (hΦ _)]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem proof : BlockResolutionInterpIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  exact interp_integral_eq d.R (hdeg.trans d.deg.symm) d.semipos.1 hA'
    (blockInterpPot d d.A A') (fun _ _ _ _ => rfl)

end BlockResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
