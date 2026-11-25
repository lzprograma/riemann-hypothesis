module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegreeIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockResolutionDegreeIntegral

theorem mInt_congr_of_locDens {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Ψ : Fin e → LocPot X} (h : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Ψ j y)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [h j y hy]
  · rfl

variable {D : ℕ} {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)}

theorem ratio_smul {A₀ A₁ : HermLine ι} (hdeg : A₁.a = A₀.a) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) :
    A₁.h (fun p => c p.1 * z p) / A₀.h (fun p => c p.1 * z p) = A₁.h z / A₀.h z := by
  have hp : (∏ k, ‖c k‖ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A₁.smul c z hc, A₀.smul c z hc, hdeg, mul_div_mul_left _ _ hp]

theorem smooth_logRatio (R : AnRes P J D) {A₀ A₁ : HermLine ι} (hdeg : A₁.a = A₀.a)
    (h₀ : IsSmoothHerm A₀) (h₁ : IsSmoothHerm A₁) (t : ℝ) :
    R.A.Smooth (fun x => t * Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x))) := fun j => by
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U ((R.A.chart j).symm y),
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U _), ⟨hy.1, R.mem_U _⟩, ?_⟩
  have hsm := (contDiffOn_const (c := t)).mul
    ((AnResBridge.contDiffOn_potOf R h₁ ((R.A.chart j).symm y) j).sub
      (AnResBridge.contDiffOn_potOf R h₀ ((R.A.chart j).symm y) j))
  refine (hsm.mono Set.inter_subset_right).congr fun y' hy' => ?_
  obtain ⟨c, hc, hcy⟩ := R.compat ((R.A.chart j).symm y') ((R.A.chart j).symm y)
    ((R.A.chart j).symm y') ⟨R.mem_U _, hy'.2.2⟩
  have hz := (R.mem ((R.A.chart j).symm y) _ hy'.2.2).1
  change t * Real.log (A₁.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y')) /
      A₀.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y'))) =
    t * (Real.log (A₁.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) -
      Real.log (A₀.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))))
  rw [hcy, ratio_smul hdeg c hc, Real.log_div (A₁.pos _ hz).ne' (A₀.pos _ hz).ne']

theorem mInt_interpPot_eq (R : AnRes P J D) {A₀ A₁ : HermLine ι} (hdeg : A₁.a = A₀.a)
    (t : ℝ) {Φ : LocPot R.X}
    (hΦ : ∀ x y, y ∈ R.U x → Φ.φ x y = (1 - t) * Real.log (A₀.h (R.lift x y)) + t * Real.log (A₁.h (R.lift x y)))
    (g : R.X → ℝ) :
    mInt R.A (fun _ => Φ) g =
      mInt R.A (fun _ => AnResBridge.potOf R A₀ +
        LocPot.ofFun (fun x => t * Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x)))) g := by
  refine mInt_congr_of_locDens _ (fun j y hy => ?_) g
  unfold locDens
  refine _root_.ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun _ => ?_
  have hmem : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U ((R.A.chart j).symm y) ∈ 𝓝 y :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U _)).mem_nhds ⟨hy, R.mem_U _⟩
  filter_upwards [hmem] with y' hy'
  obtain ⟨c, hc, hcy⟩ := R.compat ((R.A.chart j).symm y') ((R.A.chart j).symm y)
    ((R.A.chart j).symm y') ⟨R.mem_U _, hy'.2⟩
  have hz := (R.mem ((R.A.chart j).symm y) _ hy'.2).1
  have h₀ := A₀.pos _ hz
  have h₁ := A₁.pos _ hz
  show Φ.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y') =
    Real.log (A₀.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) +
      t * Real.log (A₁.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y')) /
        A₀.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y')))
  rw [hΦ _ _ hy'.2, hcy, ratio_smul hdeg c hc, Real.log_div h₁.ne' h₀.ne']
  ring

theorem mass_eq (R : AnRes P J D) {A₀ A₁ : HermLine ι} (hdeg : A₁.a = A₀.a)
    (h₀ : IsSmoothHerm A₀) (h₁ : IsSmoothHerm A₁) (t : ℝ) {Φ : LocPot R.X}
    (hΦ : ∀ x y, y ∈ R.U x → Φ.φ x y = (1 - t) * Real.log (A₀.h (R.lift x y)) + t * Real.log (A₁.h (R.lift x y))) :
    mInt R.A (fun _ => Φ) (fun _ => 1) =
      mInt R.A (fun _ => AnResBridge.potOf R A₀) (fun _ => 1) := by
  rw [mInt_interpPot_eq R hdeg t hΦ]
  exact massIndep R.A (fun _ => AnResBridge.potOf R A₀)
    (fun _ x => t * Real.log (A₁.h (R.lift x x) / A₀.h (R.lift x x)))
    (fun _ => AnResBridge.isPotential_potOf R h₀) (fun _ => smooth_logRatio R hdeg h₀ h₁ t)

theorem mass_potOf {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [CharZero Ω]
    (hGG : GenDegGeomDeg.Statement) (d : HSMBlockDatum D K ι Ω) {A₀ : HermLine ι}
    (hdeg : A₀.a = unitDeg d.k₀) (h₀ : IsSmoothHerm A₀) :
    mInt d.R.A (fun _ => AnResBridge.potOf d.R A₀) (fun _ => 1) =
      (genDeg (mCoordIdeal d.y) D (unitDeg d.k₀) : ℝ) := by
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  let B : HermLine ι := HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl)
  have hB : IsSmoothHerm B := contDiffOn_const
  have hlog : logNorm B.inv 1 = fun _ => (1 : ℝ) := by
    funext z
    rw [logNorm_inv_one]
    simp [B, HermLine.ofWeight]
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 rfl
  have key := AnResBridge.bridge d.R hex.choose (fun _ => A₀) B.inv 1 d.arith hex.choose_spec
    (fun _ => h₀) (isSmoothHerm_inv hB) hsec
  simp only [hlog] at key
  have hg := hGG K ι Ω d.y D A₀ d.arith h₀
  rw [hdeg] at hg
  rw [← hg]
  unfold geomDeg ptsIntegral
  rw [dite_eq_left hex]
  exact key.symm

end BlockResolutionDegreeIntegral

theorem BlockResolutionDegreeIntegral.proof (hGG : GenDegGeomDeg.Statement) :
    BlockResolutionDegreeIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h0 h1 hs0 hs1 t _
  rw [BlockResolutionDegreeIntegral.mass_eq d.R (h1.trans h0.symm) hs0 hs1 t (fun _ _ _ => rfl)]
  exact BlockResolutionDegreeIntegral.mass_potOf hGG d h0 hs0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
