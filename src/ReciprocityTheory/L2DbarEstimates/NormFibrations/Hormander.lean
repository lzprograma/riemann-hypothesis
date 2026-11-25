module

public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HalfSumNormSubSq
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.TstarNormSq
public import ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
public import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
public import Mathlib.MeasureTheory.Function.L2Space
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
public import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem
import ReciprocityTheory.L2DbarEstimates.Localization.Extend

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis, ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft, ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsTer, ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish, ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports, ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn, ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport, ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply, ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe, ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous, ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph, ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\npublic import Mathlib.Analysis.Calculus.FDeriv.Symmetric\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.Calculus.ContDiff.Comp\npublic import Mathlib.Analysis.Calculus.FDeriv.Mul\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[nhds (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ nhds (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2

private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dite_eq_left hex]
  unfold wdb
  rw [hE.fderiv_eq]

private lemma d_apply_eq_wd_of_mem_source {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : d n z k g p = wd n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [d, dite_eq_left hex]
  unfold wd
  rw [hE.fderiv_eq]

private lemma differentiableAt_wdb_and_fderiv_wdb_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wdb n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hW' : HasFDerivAt (wdb n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

private lemma differentiableAt_wd_and_fderiv_wd_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wd n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wd n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) -
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.sub hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wd n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) - Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wd, div_eq_inv_mul]
  have hW' : HasFDerivAt (wd n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) -
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  ring

theorem comm (n : ℕ) (M : Type*) [TopologicalSpace M] : CommStatement n M := by
  intro z hz ph j k u x hph hu
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ nhds (z x) := e0.open_target.mem_nhds hy0
  have hcH : ContDiffAt ℝ 2 (u ∘ e0.symm) (z x) := by
    have := (hu e0 he0).contDiffAt hnb
    simpa using this
  have hcP : ContDiffAt ℝ 2 ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) := by
    have := (hph e0 he0).contDiffAt hnb
    simpa using this
  have hdH : DifferentiableAt ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) :=
    (hcH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdP : DifferentiableAt ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) :=
    (hcP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : DifferentiableAt ℝ (u ∘ e0.symm) (z x) := hcH.differentiableAt (by norm_num)
  have hsymH : ∀ v w : V n, fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcH.isSymmSndFDerivAt (by simp) v w
  have hsymP : ∀ v w : V n, fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcP.isSymmSndFDerivAt (by simp) v w
  have hloc1 : ((db n z j u) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j (u ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j u _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc2 : ((db n z j (fun y => ((ph y : ℝ) : ℂ))) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j _ _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc3 : ((fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) ∘ e0.symm) =ᶠ[nhds (z x)]
      (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) := by
    filter_upwards [hnb] with y hy
    have hp := e0.map_target hy
    rw [Function.comp_apply, d_apply_eq_wd_of_mem_source z e0 he0 k u _ hp, d_apply_eq_wd_of_mem_source z e0 he0 k _ _ hp,
      he0' hp, e0.right_inv hy]
    rfl
  have hux : u x = (u ∘ e0.symm) (z x) := by
    rw [Function.comp_apply, he0' hx0, e0.left_inv hx0]
  have hW1 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdH).2
  have hW2 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdH
  have hW3 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdP
  have hW4 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdP).2
  have hFG : fderiv ℝ (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) (z x) =
      fderiv ℝ (wd n k (u ∘ e0.symm)) (z x) - ((u ∘ e0.symm) (z x) • fderiv ℝ (wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) +
        wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) • fderiv ℝ (u ∘ e0.symm) (z x)) := by
    have h1 := HasFDerivAt.sub (DifferentiableAt.hasFDerivAt hW2.1)
      (HasFDerivAt.mul (DifferentiableAt.hasFDerivAt hH) (DifferentiableAt.hasFDerivAt hW3.1))
    exact HasFDerivAt.fderiv h1
  show (d n z k (db n z j u) x - db n z j u x * d n z k (fun y => ((ph y : ℝ) : ℂ)) x) -
      db n z j (fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) x =
    d n z k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x * u x
  rw [d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j u) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j u x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (fun y => ((ph y : ℝ) : ℂ)) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x hx0, hux]
  unfold wd wdb
  rw [hloc1.fderiv_eq, hloc2.fderiv_eq, hloc3.fderiv_eq, hFG]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hW1 (bas n k), hW1 (Complex.I • bas n k), hW2.2 (bas n j), hW2.2 (Complex.I • bas n j),
    hW3.2 (bas n j), hW3.2 (Complex.I • bas n j), hW4 (bas n k), hW4 (Complex.I • bas n k)]
  unfold wd
  rw [hsymH (bas n k) (bas n j), hsymH (bas n k) (Complex.I • bas n j),
    hsymH (Complex.I • bas n k) (bas n j), hsymH (Complex.I • bas n k) (Complex.I • bas n j),
    hsymP (bas n k) (bas n j), hsymP (bas n k) (Complex.I • bas n j),
    hsymP (Complex.I • bas n k) (bas n j), hsymP (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.E
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw\npublic import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset\npublic import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem wIbp_left (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (k : Fin n) (a b : M → ℂ) (hph : CkR n z 1 ph) (ha : Ck n z 1 a) (hb : Ck n z 1 b)
    (hc : HasCompactSupport a ∨ HasCompactSupport b) :
    (∫ x, db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      -∫ x, a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hw : Ck n z 1 (fun x => (Real.exp (-ph x) : ℂ)) := ck_expNeg n z 1 ph hph
  have hbc : Ck n z 1 (fun x => conj (b x)) := Ck.conj n z 1 b hb
  set g : M → ℂ := fun x => conj (b x) * (Real.exp (-ph x) : ℂ) with hgdef
  have hg : Ck n z 1 g := Ck.mul n z 1 _ _ hbc hw

  have hdg : ∀ x, a x * db n z k g x =
      a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) := by
    intro x
    have h1 := db_mul n z _ _ hbc hw k x
    beta_reduce at h1
    rw [hgdef, h1, db_conj n z b k x, db_expNeg n z ph hph k x, dTw, db_ofReal n z ph k x]
    simp only [map_sub, map_mul]
    ring
  have hL : (fun x => db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => db n z k a x * g x := by
    funext x
    simp only [hgdef]
    ring
  have hR : (fun x => a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => a x * db n z k g x := by
    funext x
    exact (hdg x).symm
  rw [hL, hR]
  rcases hc with hca | hcb
  · have h := integral_db_mul n z hz k g a hg ha hca
    have e1 : (fun x => db n z k a x * g x) = fun x => g x * db n z k a x := by
      funext x
      ring
    have e2 : (fun x => a x * db n z k g x) = fun x => db n z k g x * a x := by
      funext x
      ring
    rw [e1, e2, h, neg_neg]
  · have hgc : HasCompactSupport g :=
      (hcb.comp_left (map_zero (starRingEnd ℂ))).mul_right
    exact integral_db_mul n z hz k a g ha hg hgc

theorem wIbp (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : WIbpStatement n M := by
  intro z hz ph k a b hph ha hb hc
  refine ⟨wIbp_left n z hz ph k a b hph ha hb hc, ?_⟩

  have h := wIbp_left n z hz ph k b a hph hb ha hc.symm
  have h' := congrArg (starRingEnd ℂ) h
  rw [← integral_conj, map_neg, ← integral_conj] at h'
  have e1 : (fun x => dTw n z ph k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (b x * conj (dTw n z ph k a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have e2 : (fun x => a x * conj (db n z k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (db n z k b x * conj (a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [e1, e2, h', neg_neg]

end

end ReciprocityTheory.L2DbarEstimates.E
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsTer =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsTer", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem pair (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : CkR n z 2 ph) (a b : M → ℂ) (ha : Ck n z 2 a) (_hac : HasCompactSupport a)
    (hb : Ck n z 2 b) (hbc : HasCompactSupport b) (j k : Fin n) :
    (∫ x, dTw n z ph j a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      (∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z) +
        ∫ x, db n z k a x * conj (db n z j b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have ha1 : Ck n z 1 a := Ck.mono n z 1 2 (by norm_num) a ha
  have hb1 : Ck n z 1 b := Ck.mono n z 1 2 (by norm_num) b hb
  have hE := ck_expNeg n z 1 ph hph1
  have hdTa : Ck n z 1 (dTw n z ph j a) := ck_dTw n z 1 ph j a hph ha
  have hdba : Ck n z 1 (db n z k a) := Ck.db n z 1 k a ha
  have s1 := wIbp_left n z hz ph k (dTw n z ph j a) b hph1 hdTa hb1 (Or.inr hbc)
  have s3 := ((wIbp n M) z hz ph j (db n z k a) b hph1 hdba hb1 (Or.inr hbc)).2
  have hcomm : ∀ x, db n z k (dTw n z ph j a) x = dTw n z ph j (db n z k a) x -
      d n z j (db n z k (fun y => (ph y : ℂ))) x * a x := by
    intro x
    have := comm n M z hz ph k j a x hph ha
    linear_combination -this
  have hcb : Continuous (fun x => conj (b x)) := Ck.continuous n z hz 1 _ (Ck.conj n z 1 b hb1)
  have hcE : Continuous (fun x => (Real.exp (-ph x) : ℂ)) := Ck.continuous n z hz 1 _ hE
  have hint1 : Integrable (fun x => dTw n z ph j (db n z k a) x * conj (b x) *
      (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact ((Ck.continuous n z hz 0 _ (ck_dTw n z 0 ph j (db n z k a) hph1 hdba)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have hint2 : Integrable (fun x => d n z j (db n z k (fun y => (ph y : ℂ))) x * a x *
      conj (b x) * (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact (((Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))).mul
        (Ck.continuous n z hz 1 _ ha1)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have e2 : ∫ x, db n z k (dTw n z ph j a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z =
      (∫ x, dTw n z ph j (db n z k a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) -
        ∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z := by
    rw [← integral_sub hint1 hint2]
    congr 1
    funext x
    rw [hcomm x]
    ring
  rw [e2, s3] at s1
  linear_combination s1

end

end ReciprocityTheory.L2DbarEstimates.E
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsTer =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HalfSumNormSubSq\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsTer\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero\npublic import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem integral_re_double_sum {M : Type*} [MeasurableSpace M] (μ : Measure M) (n : ℕ)
    (h : Fin n → Fin n → M → ℂ) (hi : ∀ j k, Integrable (h j k) μ) :
    ∫ x, (∑ j, ∑ k, h j k x).re ∂μ = (∑ j, ∑ k, ∫ x, h j k x ∂μ).re := by
  have hint : Integrable (fun x => ∑ j, ∑ k, h j k x) μ :=
    MeasureTheory.integrable_finsetSum _ fun j _ => MeasureTheory.integrable_finsetSum _ fun k _ => hi j k
  have h1 := integral_re (𝕜 := ℂ) hint
  simp only [RCLike.re_to_complex] at h1
  rw [h1, MeasureTheory.integral_finsetSum _ fun j _ => MeasureTheory.integrable_finsetSum _ fun k _ => hi j k]
  congr 1
  exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_finsetSum _ fun k _ => hi j k

theorem hasCompactSupport_of_vanish {M : Type*} [TopologicalSpace M] (u F : M → ℂ)
    (hu : HasCompactSupport u) (h : ∀ x, u x = 0 → F x = 0) : HasCompactSupport F :=
  hu.mono' fun x hx => subset_tsupport u (mt (h x) hx)

theorem basicIdentity (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    BasicIdentityStatement n M := by
  intro z hz ph f hph hf
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have hE : Ck n z 1 (fun x => (Real.exp (-ph x) : ℂ)) := ck_expNeg n z 1 ph hph1
  have hEc : Continuous (fun x => (Real.exp (-ph x) : ℂ)) := Ck.continuous n z hz 1 _ hE
  have hFc : ∀ j, Continuous (fun y => f y j) := fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hTc : ∀ j, Continuous (dTw n z ph j (fun y => f y j)) :=
    fun j => Ck.continuous n z hz 1 _ (ck_dTw n z 1 ph j _ hph (hf j).1)
  have hDc : ∀ j k, Continuous (db n z k (fun y => f y j)) :=
    fun j k => Ck.continuous n z hz 1 _ (Ck.db n z 1 k _ (hf j).1)
  have hLc : ∀ j k, Continuous (d n z j (db n z k (fun y => (ph y : ℂ)))) :=
    fun j k => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))
  have hcc : ∀ {g : M → ℂ}, Continuous g → Continuous (fun x => conj (g x)) :=
    fun hg => Complex.continuous_conj.comp hg

  set D : Fin n → Fin n → M → ℂ := fun j k x => dTw n z ph j (fun y => f y j) x *
    conj (dTw n z ph k (fun y => f y k) x) * (Real.exp (-ph x) : ℂ) with hD
  set L : Fin n → Fin n → M → ℂ := fun j k x => d n z j (db n z k (fun y => (ph y : ℂ))) x *
    f x j * conj (f x k) * (Real.exp (-ph x) : ℂ) with hL
  set C : Fin n → Fin n → M → ℂ := fun j k x => db n z k (fun y => f y j) x *
    conj (db n z j (fun y => f y k) x) * (Real.exp (-ph x) : ℂ) with hC
  set Q : Fin n → Fin n → M → ℂ := fun j k x => db n z k (fun y => f y j) x *
    conj (db n z k (fun y => f y j) x) * (Real.exp (-ph x) : ℂ) with hQ
  have iD : ∀ j k, Integrable (D j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hTc j).mul (hcc (hTc k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_dTw n z ph j _ (hf j).2) (fun x h0 => by simp [hD, h0])
  have iL : ∀ j k, Integrable (L j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact (((hLc j k).mul (hFc j)).mul (hcc (hFc k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _ (hf j).2 (fun x h0 => by simp [hL, h0])
  have iC : ∀ j k, Integrable (C j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hDc j k).mul (hcc (hDc k j))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_db n z k _ (hf j).2) (fun x h0 => by simp [hC, h0])
  have iQ : ∀ j k, Integrable (Q j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hDc j k).mul (hcc (hDc j k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_db n z k _ (hf j).2) (fun x h0 => by simp [hQ, h0])
  have iQC : ∀ j k, Integrable (fun x => Q j k x - C j k x) (vol n z) :=
    fun j k => (iQ j k).sub (iC j k)

  have pA : ∀ x, ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) =
      (∑ j, ∑ k, D j k x).re := by
    intro x
    rw [norm_sum_sq_eq]
    simp only [hD, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have pL : ∀ x, (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) =
      (∑ j, ∑ k, L j k x).re := by
    intro x
    simp only [Levi, hL, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have hnq : ∀ w : ℂ, ‖w‖ ^ 2 = (w * conj w).re := by
    intro w
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have pQ : ∀ x, (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) =
      (∑ j, ∑ k, Q j k x).re := by
    intro x
    simp only [hQ, hnq, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have pS : ∀ x, sq2 n (sbar n z f x) * Real.exp (-ph x) =
      (∑ j, ∑ k, (Q j k x - C j k x)).re := by
    intro x
    have h := half_sum_norm_sub_sq (fun j k => db n z j (fun y => f y k) x)
    simp only at h
    unfold sq2 sbar
    rw [h]
    simp only [hQ, hC, hnq, Complex.re_sum, Complex.sub_re, Complex.re_mul_ofReal,
      Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  have hA := integral_re_double_sum (vol n z) n D iD
  have hLi := integral_re_double_sum (vol n z) n L iL
  have hQi := integral_re_double_sum (vol n z) n Q iQ
  have hSi := integral_re_double_sum (vol n z) n (fun j k x => Q j k x - C j k x) iQC
  have hpair : ∀ j k, ∫ x, D j k x ∂vol n z = (∫ x, L j k x ∂vol n z) + ∫ x, C j k x ∂vol n z :=
    fun j k => pair n z hz ph hph (fun y => f y j) (fun y => f y k) (hf j).1 (hf j).2
      (hf k).1 (hf k).2 j k
  have hsub : ∀ j k, ∫ x, (Q j k x - C j k x) ∂vol n z =
      (∫ x, Q j k x ∂vol n z) - ∫ x, C j k x ∂vol n z :=
    fun j k => integral_sub (iQ j k) (iC j k)
  rw [integral_congr_ae (Filter.Eventually.of_forall pA), integral_congr_ae (Filter.Eventually.of_forall pS),
    integral_congr_ae (Filter.Eventually.of_forall pL), integral_congr_ae (Filter.Eventually.of_forall pQ),
    hA, hLi, hQi, hSi]
  simp only [hpair, hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Complex.add_re,
    Complex.sub_re]
  ring

end

end ReciprocityTheory.L2DbarEstimates.E
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HalfSumNormSubSq\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.TstarNormSq\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem ap (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : APStatement n M := by
  intro z hz ph ψ ε f hph hψ hε hf
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have hf1 : ∀ j, Ck n z 1 (fun y => f y j) := fun j => Ck.mono n z 1 2 (by norm_num) _ (hf j).1

  have hphc : Continuous ph := Complex.continuous_re.comp (Ck.continuous n z hz 2 _ hph)
  have hEr : Continuous (fun x => Real.exp (-ph x)) := Real.continuous_exp.comp hphc.neg
  have hFc : ∀ j, Continuous (fun y => f y j) := fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hTc : ∀ j, Continuous (dTw n z ph j (fun y => f y j)) :=
    fun j => Ck.continuous n z hz 1 _ (ck_dTw n z 1 ph j _ hph (hf j).1)
  have hDc : ∀ j k, Continuous (db n z k (fun y => f y j)) :=
    fun j k => Ck.continuous n z hz 1 _ (Ck.db n z 1 k _ (hf j).1)
  have hLc : ∀ j k, Continuous (d n z j (db n z k (fun y => (ph y : ℂ)))) :=
    fun j k => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))
  have hψc : ∀ j, Continuous (d n z j (fun y => (ψ y : ℂ))) :=
    fun j => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ hψ)
  have hAc : Continuous (fun x => ∑ j, dTw n z ph j (fun y => f y j) x) :=
    continuous_finsetSum _ (fun j _ => hTc j)
  have hSc : Continuous (fun x => ∑ j, (dTw n z ph j (fun y => f y j) x +
      f x j * d n z j (fun y => (ψ y : ℂ)) x)) :=
    continuous_finsetSum _ (fun j _ => (hTc j).add ((hFc j).mul (hψc j)))
  have hLevic : Continuous (fun x => (Levi n z ph x (fun j => f x j)).re) := by
    unfold Levi
    exact Complex.continuous_re.comp (continuous_finsetSum _ (fun j _ =>
      continuous_finsetSum _ (fun k _ =>
        ((hLc j k).mul (hFc j)).mul (Complex.continuous_conj.comp (hFc k)))))
  have hGc : Continuous (fun x => ∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun k _ => (hDc j k).norm.pow 2))
  have hdSc : Continuous (fun x => dSqR n z ψ x) :=
    continuous_finsetSum _ (fun j _ => (hψc j).norm.pow 2)
  have hF2c : Continuous (fun x => ∑ j, ‖f x j‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => (hFc j).norm.pow 2)

  set K : Set M := ⋃ j, tsupport (fun y => f y j) with hKdef
  have hK : IsCompact K := isCompact_iUnion (fun j => (hf j).2)
  have hcs : ∀ g : M → ℝ, (∀ x, x ∉ K → g x = 0) → HasCompactSupport g :=
    fun g hg => HasCompactSupport.intro hK hg
  have v0 : ∀ x, x ∉ K → ∀ j, f x j = 0 := fun x hx j =>
    image_eq_zero_of_notMem_tsupport (f := fun y => f y j) (x := x)
      (fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩))
  have vD : ∀ x, x ∉ K → ∀ j k, db n z k (fun y => f y j) x = 0 := fun x hx j k =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (Set.mem_iUnion.2 ⟨j, tsupport_db_subset n z k _ h⟩))
  have vT : ∀ x, x ∉ K → ∀ j, dTw n z ph j (fun y => f y j) x = 0 := fun x hx j =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (Set.mem_iUnion.2 ⟨j, tsupport_dTw_subset n z ph j _ h⟩))
  have hnf : ∀ x, ‖f x‖ ^ 2 = ∑ j, ‖f x j‖ ^ 2 := fun x => EuclideanSpace.norm_sq_eq (f x)

  have iL : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x))
      (vol n z) :=
    integrable_of_continuous_real n z hz _ (hLevic.mul hEr)
      (hcs _ (fun x hx => by simp [Levi, v0 x hx]))
  have iG : Integrable (fun x => (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) *
      Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ (hGc.mul hEr)
      (hcs _ (fun x hx => by simp [vD x hx]))
  have iA : Integrable (fun x => ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 *
      Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ ((hAc.norm.pow 2).mul hEr)
      (hcs _ (fun x hx => by simp [vT x hx]))
  have iS : Integrable (fun x => ‖∑ j, (dTw n z ph j (fun y => f y j) x +
      f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ ((hSc.norm.pow 2).mul hEr)
      (hcs _ (fun x hx => by simp [vT x hx, v0 x hx]))
  have i1 : Integrable (fun x => ((Levi n z ph x (fun j => f x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x)) (vol n z) := by
    simp only [hnf]
    exact integrable_of_continuous_real n z hz _
      ((hLevic.sub ((continuous_const.mul hdSc).mul hF2c)).mul hEr)
      (hcs _ (fun x hx => by simp [Levi, v0 x hx]))

  have hpt : ∀ x, ((Levi n z ph x (fun j => f x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x) ≤
      (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) -
        ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) +
        (1 + ε) * (‖∑ j, (dTw n z ph j (fun y => f y j) x +
          f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x)) := by
    intro x
    have hsplit : (∑ j, (dTw n z ph j (fun y => f y j) x +
        f x j * d n z j (fun y => (ψ y : ℂ)) x)) =
        (∑ j, dTw n z ph j (fun y => f y j) x) +
          ∑ j, f x j * d n z j (fun y => (ψ y : ℂ)) x := Finset.sum_add_distrib
    have h1 := norm_sq_le_split (∑ j, dTw n z ph j (fun y => f y j) x)
      (∑ j, f x j * d n z j (fun y => (ψ y : ℂ)) x) ε hε
    rw [← hsplit] at h1
    have h2 := norm_sum_mul_sq_le (fun j => f x j) (fun j => d n z j (fun y => (ψ y : ℂ)) x)
    have hc : 0 ≤ 1 + 1 / ε := by positivity
    have he : 0 < Real.exp (-ph x) := Real.exp_pos _
    have hG0 : 0 ≤ ∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2 := by positivity
    have h3 : ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 ≤
        (1 + ε) * ‖∑ j, (dTw n z ph j (fun y => f y j) x +
          f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 +
          (1 + 1 / ε) * (dSqR n z ψ x * ‖f x‖ ^ 2) := by
      rw [hnf x]
      unfold dSqR
      nlinarith [mul_le_mul_of_nonneg_left h2 hc]
    nlinarith [mul_le_mul_of_nonneg_right h3 he.le, mul_nonneg hG0 he.le]

  have hmono : ∫ x, ((Levi n z ph x (fun j => f x j)).re - (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x) ∂vol n z ≤
      (∫ x, (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) ∂vol n z) +
        (∫ x, (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) ∂vol n z) -
        (∫ x, ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) ∂vol n z) +
        (1 + ε) * ∫ x, ‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x) ∂vol n z := by
    have j1 : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x)) (vol n z) := iL.add iG
    have j2 : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) - ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x)) (vol n z) := j1.sub iA
    have j3 : Integrable (fun x => (1 + ε) * (‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x))) (vol n z) := iS.const_mul (1 + ε)
    rw [← integral_add iL iG, ← integral_sub j1 iA, ← integral_const_mul, ← integral_add j2 j3]
    exact integral_mono i1 (j2.add j3) hpt
  have hB := basicIdentity n M z hz ph f hph hf
  have hT : ∫ x, ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
      Real.exp (-(ph x - 2 * ψ x)) ∂vol n z =
      ∫ x, ‖∑ j, (dTw n z ph j (fun y => f y j) x +
        f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x) ∂vol n z := by
    congr 1
    funext x
    exact tstar_norm_sq n z hz ph ψ f hph1 hψ hf1 x
  rw [hT]
  linarith

end

end ReciprocityTheory.L2DbarEstimates.E
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\npublic import Mathlib.Analysis.Calculus.FDeriv.Symmetric\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.Calculus.ContDiff.Basic\npublic import Mathlib.Analysis.Calculus.ContDiff.Comp\npublic import Mathlib.Analysis.Calculus.ContDiff.Operations\npublic import Mathlib.Analysis.Calculus.FDeriv.Mul\n\n"}
section -- clump:auto
@[expose] public section

end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Mathlib.Topology.UniformSpace.Uniformizable\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

theorem Kernel.hasCompactSupport (K : Kernel E μ) : HasCompactSupport K.toFun :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun x hx => by
    by_contra h
    exact hx (ball_subset_closedBall (K.support_subset h))

end

theorem moll_smooth (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothSt E μ := fun K _ hu =>
  K.hasCompactSupport.contDiff_convolution_left _ K.smooth hu

theorem moll_support (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SupportSt E μ := by
  intro K u
  refine (support_convolution_subset _).trans ?_
  rw [add_comm]
  exact Set.add_subset_add_left K.support_subset

theorem kernel_std (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : StdSt E μ := by
  have h : (fun ε : ℝ => (Kernel.std E μ ε).r) =ᶠ[𝓝[>] 0] id := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [Kernel.std, Kernel.ofBump, stdBump, show (0 : ℝ) < ε from hε]
  exact (tendsto_congr' h).2 (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)

end ReciprocityTheory.L2DbarEstimates.B
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Mathlib.Topology.UniformSpace.Uniformizable\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem fderiv_moll_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : LocallyIntegrable u μ)
    (x a : E) :
    fderiv ℝ (moll K u) x a = ∫ y, (fderiv ℝ K.toFun (x - y) a) • u y ∂μ := by
  have hcs : HasCompactSupport K.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun y hy => by
      by_contra h
      exact hy (ball_subset_closedBall (K.support_subset h))
  have hd := hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (K.smooth.of_le (by simp)) hu x
  have hmoll : moll K u = K.toFun ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u := rfl
  rw [hmoll, hd.fderiv]
  have hex := (hcs.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (K.smooth.continuous_fderiv (by simp)) hu x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  rw [← integral_sub_left_eq_self _ μ x]
  congr 1
  ext y
  rw [sub_sub_cancel]
  rfl

theorem moll_weakComm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : WeakCommSt E μ := by
  intro m c v g w hw K
  funext x
  have hd : ∀ k, fderiv ℝ (moll K (g k)) x (v k) =
      ∫ y, (fderiv ℝ K.toFun (x - y) (v k)) • g k y ∂μ :=
    fun k => fderiv_moll_apply E μ K (hw.1 k) x (v k)
  set φ : E → ℂ := fun y => ((K.toFun (x - y) : ℝ) : ℂ) with hφdef
  have hφs : ContDiff ℝ ∞ φ :=
    Complex.ofRealCLM.contDiff.comp (K.smooth.comp (contDiff_const.sub contDiff_id))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall x K.r) fun y hy => by
      simp only [hφdef, Complex.ofReal_eq_zero]
      by_contra h
      apply hy
      have h' := K.support_subset h
      rw [mem_ball_zero_iff] at h'
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact h'.le
  have hw3 := hw.2.2 φ hφs hφc
  have hdφ : ∀ y a, fderiv ℝ φ y a = -((fderiv ℝ K.toFun (x - y) a : ℝ) : ℂ) := by
    intro y a
    have h1 : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((K.smooth.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    rw [(show HasFDerivAt φ _ y from h3).fderiv]
    simp
  have hm : moll K w x = ∫ y, w y * φ y ∂μ := by
    show ∫ t, K.toFun t • w (x - t) ∂μ = _
    rw [← integral_sub_left_eq_self (fun t => K.toFun t • w (x - t)) μ x]
    congr 1
    ext y
    simp only [hφdef, sub_sub_cancel, Complex.real_smul]
    ring
  simp only [Dop, hd]
  rw [hm, hw3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_neg, ← integral_neg]
  congr 2
  ext y
  rw [hdφ, Complex.real_smul]
  ring

end ReciprocityTheory.L2DbarEstimates.B
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem Kernel.lintegral_ofReal (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) :
    ∫⁻ t, ENNReal.ofReal (K.toFun t) ∂μ = 1 := by
  have hint : Integrable K.toFun μ :=
    Integrable.of_integral_ne_zero (by rw [K.integral_eq_one]; exact one_ne_zero)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall K.nonneg),
    K.integral_eq_one, ENNReal.ofReal_one]

theorem moll_enorm_sq_le (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : AEStronglyMeasurable u μ)
    (x : E) :
    ‖moll K u x‖ₑ ^ 2 ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
  have hK0 := K.nonneg
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  have h1 : ‖moll K u x‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    have hmoll : moll K u x = ∫ t, K.toFun t • u (x - t) ∂μ := rfl
    rw [hmoll]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (hK0 t)]
  have hum : AEMeasurable (fun t => ‖u (x - t)‖ₑ) μ :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)).enorm
  set f : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) with hfdef
  set g : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) * ‖u (x - t)‖ₑ with hgdef
  have hf : AEMeasurable f μ := hKm.sqrt.ennreal_ofReal.aemeasurable
  have hg : AEMeasurable g μ := hf.mul hum
  have r2 : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z ^ 2 := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have hsq : ∀ t, ENNReal.ofReal (Real.sqrt (K.toFun t)) ^ 2 = ENNReal.ofReal (K.toFun t) := by
    intro t
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hK0 t)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : ∫⁻ t, (f * g) t ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply, hfdef, hgdef]
    rw [← mul_assoc, ← pow_two, hsq]
  have e2 : ∫⁻ t, f t ^ (2 : ℝ) ∂μ = 1 := by
    rw [← Kernel.lintegral_ofReal E μ K]
    refine lintegral_congr fun t => ?_
    simp only [hfdef]
    rw [r2, hsq]
  have e3 : ∫⁻ t, g t ^ (2 : ℝ) ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [hgdef]
    rw [r2, mul_pow, hsq]
  rw [e1, e2, e3, ENNReal.one_rpow, one_mul] at hH
  calc ‖moll K u x‖ₑ ^ 2
      ≤ ((∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1.trans hH) 2
    _ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem moll_young_sq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) (u : E → ℂ) (s : Set E) (hs : MeasurableSet s)
    (hu : AEStronglyMeasurable u μ) :
    ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ ≤ ∫⁻ y in thickening K.r s, ‖u y‖ₑ ^ 2 ∂μ := by
  set T := thickening K.r s with hTdef
  have hT : MeasurableSet T := isOpen_thickening.measurableSet
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  set F : E → E → ℝ≥0∞ := fun x t => ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 with hFdef
  have hF : AEMeasurable (Function.uncurry F) ((μ.restrict s).prod μ) := by
    have hq := hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
    have hF0 : AEMeasurable (Function.uncurry F) (μ.prod μ) :=
      (hKm.comp measurable_snd).ennreal_ofReal.aemeasurable.mul (hq.enorm.pow_const 2)
    exact hF0.mono_ac (Measure.restrict_le_self.absolutelyContinuous.prod
      (Measure.AbsolutelyContinuous.refl μ))
  have htrans : ∀ t, ∫⁻ x in (fun x => x - t) ⁻¹' T, ‖u (x - t)‖ₑ ^ 2 ∂μ =
      ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    rw [← lintegral_indicator (hT.preimage (measurable_sub_const t)), ← lintegral_indicator hT,
      ← lintegral_sub_right_eq_self (T.indicator fun y => ‖u y‖ₑ ^ 2) t]
    refine lintegral_congr fun x => ?_
    first
    | rfl
  have hpt : ∀ t, ∫⁻ x in s, F x t ∂μ ≤ ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    simp only [hFdef]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    by_cases h0 : K.toFun t = 0
    · simp [h0]
    · have ht : t ∈ ball (0 : E) K.r := K.support_subset h0
      refine mul_le_mul' le_rfl ?_
      rw [← htrans t]
      refine lintegral_mono_set fun x hx => ?_
      simp only [Set.mem_preimage, hTdef]
      refine mem_thickening_iff.mpr ⟨x, hx, ?_⟩
      rw [mem_ball_zero_iff] at ht
      simpa [dist_eq_norm] using ht
  calc ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in s, ∫⁻ t, F x t ∂μ ∂μ :=
        lintegral_mono fun x => moll_enorm_sq_le E μ K hu x
    _ = ∫⁻ t, ∫⁻ x in s, F x t ∂μ ∂μ := lintegral_lintegral_swap hF
    _ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ ∂μ := lintegral_mono hpt
    _ = ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
        rw [lintegral_mul_const _ hKm.ennreal_ofReal, Kernel.lintegral_ofReal E μ K, one_mul]

theorem moll_young (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : YoungSt E μ := by
  intro K u s hs hu
  have h := moll_young_sq E μ K u s hs hu
  have e : ∀ z : ℝ≥0∞, z ^ (ENNReal.toReal 2) = z ^ 2 := fun z => by
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]; norm_num
  have huT : AEStronglyMeasurable u (μ.restrict (thickening K.r s)) := hu.restrict
  have hmoll : AEStronglyMeasurable (moll K u) μ := by
    have hq := hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
    have hprod : AEStronglyMeasurable
        (fun p : E × E => K.toFun p.2 • u (p.1 - p.2)) (μ.prod μ) :=
      (K.smooth.continuous.measurable.comp measurable_snd).aestronglyMeasurable.smul hq
    change AEStronglyMeasurable
      (fun x => ∫ t, K.toFun t • u (x - t) ∂μ) μ
    exact hprod.integral_prod_right'
  have hmolls : AEStronglyMeasurable (moll K u) (μ.restrict s) := hmoll.restrict
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) huT,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmolls]
  simp_rw [e]
  exact ENNReal.rpow_le_rpow h (by norm_num)

end ReciprocityTheory.L2DbarEstimates.B
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.MeasureTheory.Function.ContinuousMapDense\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Mathlib.Topology.UniformSpace.Uniformizable\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem moll_tendsto_of_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} {K : ι → Kernel E μ}
    (hK : Tendsto (fun i => (K i).r) l (𝓝 0)) {g : E → ℂ} (hgs : HasCompactSupport g)
    (hgc : Continuous g) : Tendsto (fun i => eLpNorm (moll (K i) g - g) 2 μ) l (𝓝 0) := by
  have hgu : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
  set S := Metric.cthickening 1 (tsupport g) with hS
  have hSc : IsCompact S := hgs.isCompact.cthickening
  set C := μ S ^ ((2 : ℝ≥0∞).toReal⁻¹) with hC
  have hCfin : C ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hSc.measure_lt_top.ne
  have hgm : AEStronglyMeasurable g μ := hgc.aestronglyMeasurable
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, eLpNorm (moll (K i) g - g) 2 μ ≤ C * ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨ρ, hρ, hρg⟩ := Metric.uniformContinuous_iff.1 hgu δ hδ
    filter_upwards [hK.eventually (gt_mem_nhds (lt_min hρ one_pos))] with i hi
    have hr : (K i).r < ρ := lt_of_lt_of_le hi (min_le_left _ _)
    have hr1 : (K i).r < 1 := lt_of_lt_of_le hi (min_le_right _ _)
    have hbound : ∀ x, ‖(moll (K i) g - g) x‖ ≤ δ := by
      intro x
      rw [Pi.sub_apply, ← dist_eq_norm]
      simp only [moll]
      exact dist_convolution_le hδ.le (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
        (fun y hy => (hρg (lt_trans (mem_ball.1 hy) hr)).le)
    have hsupp : Function.support (moll (K i) g - g) ⊆ S := by
      intro x hx
      by_contra hxS
      apply hx
      have hx0 : ∀ y ∈ ball x (K i).r, g y = 0 := by
        intro y hy
        by_contra hy0
        apply hxS
        refine Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hy0) ?_
        rw [dist_comm]; exact le_of_lt (lt_trans (mem_ball.1 hy) hr1)
      have hgx : g x = 0 := hx0 x (mem_ball_self (K i).r_pos)
      have h0 : dist (moll (K i) g x) (0 : ℂ) ≤ 0 := by
        simp only [moll]
        exact dist_convolution_le le_rfl (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
          (fun y hy => by rw [hx0 y hy, dist_self])
      rw [Pi.sub_apply, hgx, sub_zero]
      exact dist_le_zero.1 h0
    have hKcs : HasCompactSupport (K i).toFun :=
      HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by
        by_contra h
        exact hx (ball_subset_closedBall ((K i).support_subset h)))
    have hKc : Continuous (K i).toFun := (K i).smooth.continuous
    have hgL : LocallyIntegrable g μ := hgc.locallyIntegrable
    have hc : Continuous (moll (K i) g - g) :=
      (hKcs.continuous_convolution_left _ hKc hgL).sub hgc
    rw [← eLpNorm_restrict_eq_of_support_subset hc.aestronglyMeasurable hsupp]
    refine (eLpNorm_le_of_ae_bound (μ := μ.restrict S) hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)).trans ?_
    rw [Measure.restrict_apply_univ]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nnreal_pos_mul_lt hCfin hε.ne'
  filter_upwards [key n (NNReal.coe_pos.2 hn)] with i hi
  refine hi.trans ?_
  rw [ENNReal.ofReal_coe_nnreal, mul_comm]
  exact hnε.le

theorem moll_l2Tendsto (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : MollifierL2Tendsto E μ ι := by
  intro l K hK u hu
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hη : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by simp)).ne'
  obtain ⟨g, hgs, hug, hgc, hgL⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hη
  have hmid := moll_tendsto_of_continuous E μ hK hgs hgc
  rw [ENNReal.tendsto_nhds_zero] at hmid
  filter_upwards [hmid (ε / 3) (pos_iff_ne_zero.2 hη)] with i hi
  have hcs : HasCompactSupport (K i).toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall ((K i).support_subset h)))
  have hKc : Continuous (K i).toFun := (K i).smooth.continuous
  have hug' : MemLp (u - g) 2 μ := hu.sub hgL
  have hli : LocallyIntegrable (u - g) μ := hug'.locallyIntegrable (by norm_num)
  have hgli : LocallyIntegrable g μ := hgL.locallyIntegrable (by norm_num)
  have hlin : moll (K i) u = moll (K i) (u - g) + moll (K i) g := by
    simp only [moll]
    rw [← ConvolutionExists.distrib_add (hcs.convolutionExists_left _ hKc hli)
      (hcs.convolutionExists_left _ hKc hgli), sub_add_cancel]
  have hc1 : Continuous (moll (K i) (u - g)) := hcs.continuous_convolution_left _ hKc hli
  have hc2 : Continuous (moll (K i) g) := hcs.continuous_convolution_left _ hKc hgli
  have hdec : moll (K i) u - u = moll (K i) (u - g) + (moll (K i) g - g) + (g - u) := by
    rw [hlin]; abel
  have hY : eLpNorm (moll (K i) (u - g)) 2 μ ≤ eLpNorm (u - g) 2 μ := by
    have h := moll_young E μ (K i) (u - g) Set.univ MeasurableSet.univ hug'.aestronglyMeasurable
    have hth : thickening (K i).r (Set.univ : Set E) = Set.univ :=
      Set.eq_univ_of_forall fun x => Metric.self_subset_thickening (K i).r_pos _ (Set.mem_univ x)
    simp only [hth, Measure.restrict_univ] at h
    exact h
  rw [hdec]
  calc eLpNorm (moll (K i) (u - g) + (moll (K i) g - g) + (g - u)) 2 μ
      ≤ eLpNorm (moll (K i) (u - g) + (moll (K i) g - g)) 2 μ + eLpNorm (g - u) 2 μ :=
        eLpNorm_add_le (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    _ ≤ eLpNorm (moll (K i) (u - g)) 2 μ + eLpNorm (moll (K i) g - g) 2 μ + eLpNorm (g - u) 2 μ := by
        gcongr
        exact eLpNorm_add_le (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hY.trans hug
        · rw [eLpNorm_sub_comm]; exact hug
    _ = ε := ENNReal.add_thirds ε

end ReciprocityTheory.L2DbarEstimates.B
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem moll_graph (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : GraphSt E μ ι := by
  intro l K hK m c v g w hw hg hw2
  refine ⟨fun k => moll_l2Tendsto E μ ι l K hK (g k) (hg k), ?_⟩
  refine (moll_l2Tendsto E μ ι l K hK w hw2).congr ?_
  intro i
  rw [moll_weakComm E μ m c v g w hw (K i)]

end ReciprocityTheory.L2DbarEstimates.B
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement\npublic import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports\nimport ReciprocityTheory.L2DbarEstimates.BasicIdentity.TstarNormSq\npublic import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed\npublic import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf\nimport ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem\npublic import ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn\nimport ReciprocityTheory.L2DbarEstimates.Localization.Extend\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport\npublic import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph\npublic import ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply\npublic import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall\n\n"}
section -- clump:auto
@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory

theorem regMAll (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : F.RegMStatement n M :=
  F.regM n M C.reg (F.extend n M)

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : HStatement n M :=
  F.hStatement_of n M (E.ap n M) (E.tStarIbp n M) (chain n M) C.reg
    (B.moll_graph (V n) volume ℝ) (B.moll_smooth (V n) volume) (B.moll_support (V n) volume)
    (B.kernel_std (V n) volume)

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SStatement n M :=
  H.skoda n M (fun p => hormander n (M × Fin p))
    (fun p => F.needBergmanClosed n (M × Fin p) (regMAll n (M × Fin p)))

end ReciprocityTheory.L2DbarEstimates
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander =====
