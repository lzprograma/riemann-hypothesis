module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.RatFormPosOfIntPos
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Pi.Interval
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.Instances.Matrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan


open Matrix in
theorem posDef_coercive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ, ε * ‖x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x) := by
    intro x hx
    simpa using (Matrix.posDef_iff_dotProduct_mulVec.1 hA).2 hx
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x) := by
    apply Continuous.dotProduct continuous_id
    exact Continuous.matrix_mulVec continuous_const continuous_id
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere _ _
  have key : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.sphere (0 : Fin n → ℝ) 1, ε ≤ x ⬝ᵥ (A *ᵥ x) := by
    rcases (Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos x0 ?_, fun x hx => hmin hx⟩
      rintro rfl
      simp at hx0
  obtain ⟨ε, hε, hb⟩ := key
  refine ⟨ε, hε, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hb _ hu
  have e : (‖x‖⁻¹ • x) ⬝ᵥ (A *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [sq, mul_assoc]
  rw [e] at h1
  have h2 : 0 < ‖x‖ ^ 2 := by positivity
  calc ε * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x))) * ‖x‖ ^ 2 := by gcongr
    _ = x ⬝ᵥ (A *ᵥ x) := by field_simp


open Matrix in
theorem sublevel_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) →
    ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  intros
  apply GlobalTheory.ToricData.finite_form_le <;> assumption

end GlobalTheory.CompanionTheory.Ar.Fan
