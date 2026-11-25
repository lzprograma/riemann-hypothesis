module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_mem_layer_of_inK {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) :
    actM E Z x ∈ layer ε E V k := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h ⊢ <;>
      first | exact h | linear_combination h / 2 | linear_combination -h / 2
  rw [actM, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  by_cases hab : ε a = ε b
  · exact Submodule.smul_mem _ _ (layer_kStable hE hV k a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact zero_mem _

theorem actM_pow_mem_layer_of_inK {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ layer ε E V k :=
  Module.End.pow_apply_mem_of_forall_mem m (fun _ => actM_mem_layer_of_inK hE hV hZ) x hx

theorem exists_norm_actM_pow_le_of_inK {V : Submodule ℂ D} (hE : IsGlRep E)
    (hV : IsKStableSub ε E V) (hVf : FiniteDimensional ℂ V) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : inK ε Z) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ layer ε E V k, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hVf k
  let T : layer ε E V k →ₗ[ℂ] layer ε E V k :=
    (actM E Z).restrict (fun x hx => actM_mem_layer_of_inK hE hV hZ hx)
  let T' := Module.End.toContinuousLinearMap (layer ε E V k) T
  refine ⟨‖T'‖, norm_nonneg _, fun x hx m => ?_⟩
  rcases m with _ | m
  · simp
  · have hpow : ((actM E Z) ^ (m + 1)) x = (((T' ^ (m + 1)) ⟨x, hx⟩ : layer ε E V k) : D) := by
      have e : T' ^ (m + 1) = Module.End.toContinuousLinearMap (layer ε E V k) (T ^ (m + 1)) :=
        (map_pow (Module.End.toContinuousLinearMap (layer ε E V k)) T (m + 1)).symm
      rw [e, Module.End.pow_restrict]; rfl
    rw [hpow]
    calc ‖(T' ^ (m + 1)) ⟨x, hx⟩‖
        ≤ ‖T' ^ (m + 1)‖ * ‖(⟨x, hx⟩ : layer ε E V k)‖ := (T' ^ (m + 1)).le_opNorm _
      _ ≤ ‖T'‖ ^ (m + 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (norm_pow_le' T' m.succ_pos) (norm_nonneg _)

theorem exp_inK_apply_mem_closure (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {v : D} (hv : v ∈ genSub E V) :
    σ (NormedSpace.exp Z) (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hE := hD.glRep
  have hv' := hv
  rw [genSub_eq_iSup_layer hE hVK] at hv'
  obtain ⟨k, hk⟩ : ∃ k, v ∈ layer ε E V k :=
    (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun i j hij => layer_mono hij)).mp hv'
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_inK hE hVK hVf hZ k
  have hs : Summable fun m : ℕ => C ^ m * ‖v‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_left ‖v‖
    refine this.congr fun m => ?_
    simp only [sub_zero, abs_one, one_pow, mul_one]
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖)
    (fun m => by simpa using hC v hk m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, Complex.ofReal_one,
    one_smul, ContinuousLinearMap.one_apply, sub_zero, one_pow] at hsum
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_map_of_mem
    (layer_le_genSub (ε := ε) k (actM_pow_mem_layer_of_inK hE hVK hZ hk m))

end Rep

end ReciprocityTheory.ChartRestriction.DS
