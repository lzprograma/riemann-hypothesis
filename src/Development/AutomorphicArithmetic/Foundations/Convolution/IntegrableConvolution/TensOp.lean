module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Mathlib.Tactic.Linter.Style

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

section General

variable {G Γ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem inner_cc (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (π : UnitaryRep G H)
    (f : CompactlySupportedContinuousMap G ℂ) (w v : H) :
    ⟪w, π.integrated μ (UnitaryRep.ccToL1 μ f) v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  have hint : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  rw [UnitaryRep.integrated_ccToL1_apply, ← integral_inner hint]
  simp only [inner_smul_right]

private theorem inner_ofFn_prod (μ : Measure G) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (π : UnitaryRep Γ H) : ∀ (k : ℕ) (s : Fin k → G →* Γ) (hs : ∀ i, Continuous (s i))
    (φ : Fin k → CompactlySupportedContinuousMap G ℂ) (w v : H),
    ⟪w, (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated μ (UnitaryRep.ccToL1 μ (φ i))).prod v⟫_ℂ =
      ∫ g : Fin k → G, (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ
        ∂(Measure.pi fun _ => μ) := by
  intro k
  induction k with
  | zero =>
    intro s hs φ w v
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) (fun i => i.elim0), integral_dirac]
    simp
  | succ k ih =>
    intro s hs φ w v
    have hint : ∀ i, Integrable (φ i) μ := fun i =>
      (φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport
    have hF : Integrable (fun g : Fin (k + 1) → G =>
        (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ)
        (Measure.pi fun _ => μ) := by
      refine (Integrable.fintype_prod (f := fun i => (φ i : G → ℂ)) hint).mul_bdd
        (c := ‖w‖ * ‖v‖) ?_ (Filter.Eventually.of_forall fun g => π.norm_inner_orbit_le w v _)
      have hc : Continuous fun g : Fin (k + 1) → G =>
          (List.ofFn fun i => s i (g i)).prod := by
        simp_rw [List.ofFn_eq_map]
        exact continuous_list_prod _ fun i _ => (hs i).comp (continuous_apply i)
      exact (continuous_const.inner ((π.continuous_orbit v).comp hc)).aestronglyMeasurable
    have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0).symm
    rw [← mp.integral_comp' _]
    refine Eq.trans ?_ (integral_prod _ (mp.integrable_comp_of_integrable hF)).symm
    rw [List.ofFn_succ, List.prod_cons, ContinuousLinearMap.mul_apply, inner_cc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [UnitaryRep.compHom_apply]
    rw [UnitaryRep.inner_map_right, ih (fun i => s i.succ) (fun i => hs _) (fun i => φ i.succ),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.prod_univ_succ, List.ofFn_succ,
      List.prod_cons, Fin.insertNthEquiv_zero]
    show _ = (φ 0 x * ∏ i, φ i.succ (g i)) *
      ⟪w, π (s 0 x * (List.ofFn fun i => s i.succ (g i)).prod) v⟫_ℂ
    rw [UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right π (s 0 x) w]
    ring

end General

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.tensOp :
    UpperTheory.ConvolutionTheory.L1.TensOp := by
  intro F E _ _ _ _ _ σ m D n νE _ νF _ hν s hs hposition H _ _ _ π φ β hβ
  obtain ⟨hcg, -, hmul, hcont, -⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  have hglue : ∀ g : Fin (m + 1) → archGroup F n,
      UpperTheory.ConvolutionTheory.L1.glueA D n g = (List.ofFn fun i => s i (g i)).prod := by
    intro g
    have hg : (List.ofFn fun i =>
        (Pi.mulSingle i (g i) : Fin (m + 1) → archGroup F n)).prod = g := by
      funext j
      have e := map_list_prod (Pi.evalMonoidHom (fun _ : Fin (m + 1) => archGroup F n) j)
        (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin (m + 1) → archGroup F n))
      simp only [Pi.evalMonoidHom_apply] at e
      rw [e, List.map_ofFn, List.ofFn_eq_map, List.prod_map_eq_pow_single j _ fun i hi _ => by
        simp [Pi.mulSingle_eq_of_ne hi.symm]]
      simp
    have e := map_list_prod (MonoidHom.mk' (UpperTheory.ConvolutionTheory.L1.glueA D n) hmul)
      (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin (m + 1) → archGroup F n))
    rw [hg, List.map_ofFn] at e
    refine e.trans ?_
    congr 1
    congr 1
    funext i
    exact (hposition i (g i)).symm
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [UpperTheory.ConvolutionTheory.L1.inner_ofFn_prod, UpperTheory.ConvolutionTheory.L1.inner_cc]
  have hm : Continuous fun x : archGroup E n => β x * ⟪w, π x v⟫_ℂ :=
    β.continuous.mul (continuous_const.inner (π.continuous_orbit v))
  have e1 : ∫ x, β x * ⟪w, π x v⟫_ℂ ∂νE = ∫ x, β x * ⟪w, π x v⟫_ℂ
      ∂(Measure.map (UpperTheory.ConvolutionTheory.L1.glueA D n) (Measure.pi fun _ => νF)) := by
    rw [← hν]
  rw [e1, integral_map hcont.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [hβ, hglue g]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hglue g, hcg]
