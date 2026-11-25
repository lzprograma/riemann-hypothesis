module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

noncomputable section
namespace GlobalTheory.FockKStab
open GlobalTheory.ExpAct
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem mem_of_exp {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (hL : LocFin L) (N : Submodule ℂ V)
    (T : V) (h : ∀ s : ℝ, ∃ U : Module.End ℂ V, IsExp ((s : ℂ) • L) U ∧ U T ∈ N) : L T ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  set l : V →ₗ[ℂ] ℂ := l' ∘ₗ N.mkQ with hldef
  have hl : ∀ v ∈ N, l v = 0 := fun v hv => by simp [hldef, (Submodule.Quotient.mk_eq_zero N).2 hv]
  show l (L T) = 0
  obtain ⟨N0, hfin, hT, hN0⟩ := hL T
  set A := mat L N0 hN0
  set x := crd N0 ⟨T, hT⟩
  set φ := l ∘ₗ emb N0
  have hpow : ∀ n : ℕ, φ ((A ^ n) *ᵥ x) = l ((L ^ n) T) := fun n => by
    simp only [φ, LinearMap.comp_apply, A, emb_pow_mulVec, x, emb_crd]
  have hg : ∀ s : ℝ, φ (NormedSpace.exp (s • A) *ᵥ x) = 0 := by
    intro s
    obtain ⟨U, hU, hUN⟩ := h s
    have h1 := hU T l
    have h2 := hasSum_exp_mulVec (s • A) φ x
    have e : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ * φ (((s • A) ^ n) *ᵥ x) =
        ((n.factorial : ℂ))⁻¹ * l ((((s : ℂ) • L) ^ n) T) := fun n => by
      rw [smul_pow, smul_pow, Matrix.smul_mulVec, LinearMap.map_smul_of_tower, hpow, LinearMap.smul_apply,
        map_smul]
      simp [Complex.real_smul]
    simp only [e] at h2
    rw [h2.unique h1, hl _ hUN]
  let ψ : Matrix (Fin (Module.finrank ℂ N0)) (Fin (Module.finrank ℂ N0)) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => φ (M *ᵥ x)
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun r M => by
        rw [Matrix.smul_mulVec, LinearMap.map_smul_of_tower]; rfl }
  have hd : HasDerivAt (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A)))
      (ψ.toContinuousLinearMap (A * NormedSpace.exp ((0 : ℝ) • A))) 0 :=
    (ψ.toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const' A (0 : ℝ))
  have hz : (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A))) = fun _ => 0 := by
    funext u; exact hg u
  rw [hz] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  simp only [zero_smul, NormedSpace.exp_zero, mul_one] at this
  have e2 : ψ.toContinuousLinearMap A = l (L T) := by
    show φ (A *ᵥ x) = _
    simp only [φ, LinearMap.comp_apply, A, emb_mulVec, x, emb_crd]
  rw [← e2]; exact this

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

theorem jm_mul_jm (R S : ℕ) : Formalism.BasicNotions.TH.Jm R S * Formalism.BasicNotions.TH.Jm R S = 1 := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem commute_jm {R S : ℕ} {X : Mat R S} (hX : IsKC X) : Commute X (Formalism.BasicNotions.TH.Jm R S) := by
  show X * _ = _ * X
  have h1 : ∀ i j, X (Sum.inl i) (Sum.inr j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  have h2 : ∀ i j, X (Sum.inr i) (Sum.inl j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply, h1, h2]





theorem mem_upq {R S : ℕ} {X : Mat R S} (hX : IsKC X) (hs : Xᴴ = -X) : X ∈ upq R S := by
  show Xᴴ * _ + _ * X = 0
  rw [hs, ← (commute_jm hX).eq]; simp

theorem frame_inv {α : Type} [Fintype α] [DecidableEq α] {R S : ℕ} {M : Matrix α α ℂ} {C : Matrix α (Ix R S) ℂ}
    {A' : Matrix (Ix R S) α ℂ} (h : IsFrame M C) (hA : C * A' = 1) : A' * C = 1 := by
  set K := M * C.map star * Formalism.BasicNotions.TH.Jm R S
  have h1 : Cᵀ * K = 1 := by
    simp only [K, ← Matrix.mul_assoc, h.1, jm_mul_jm]
  have h2 : Kᵀ * C = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : A' = Kᵀ := by
    calc A' = (Kᵀ * C) * A' := by rw [h2, Matrix.one_mul]
      _ = Kᵀ := by rw [Matrix.mul_assoc, hA, Matrix.mul_one]
  rw [h3, h2]


end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

end Tensor





end GlobalTheory.FockKStab
end
