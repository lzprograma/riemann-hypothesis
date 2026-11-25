module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousDualG

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem invT_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) : (J⁻¹ᵀ)ᵀ * J = 1 := by
  rw [Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ (Ne.isUnit h.2)]

omit [NumberField F] [NumberField E] in
theorem isHermND_invT {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) : IsHermND σ J⁻¹ᵀ := by
  have hu : IsUnit J.det := Ne.isUnit h.2
  have e1 : J.map (σ : E →+* E) = Jᵀ := by
    ext i j
    exact h.1 j i
  have e2 : (Jᵀ)⁻¹ = J⁻¹.map (σ : E →+* E) := Matrix.inv_eq_left_inv (by
    rw [← e1, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨fun i j => ?_, ?_⟩
  · have := congrFun (congrFun e2 i) j
    rw [← Matrix.transpose_nonsing_inv] at this
    exact this.symm
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero

theorem LatH.swap {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    (hS : IsHermND σ JS) (hT : IsHermND σ JT) (h : LatH σ JS JT ξ₀) : LatH σ JT⁻¹ᵀ JS⁻¹ᵀ ξ₀ :=
  Sw.latH_swap σ (invT_mul hS) (invT_mul hT) ξ₀ h

theorem isDblCoord_cast₂ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Invertible (2 : R)] {ξ ξ' : A} {J J' : Matrix β β A} (h : ξ • J = ξ' • J')
    {K : Matrix α α A} {κ : Type} [Fintype κ] (d : Darboux (symp c ξ K J) κ) {dd : Darboux (symp c ξ' K (dbl J')) (κ ⊕ κ)}
    (H : IsDblCoord c ξ' K J' (GlobalTheory.WeilSchrodinger.transD c (Sw.castD c h (GlobalTheory.WeilSchrodinger.transD c d))) dd) :
    IsDblCoord c ξ K J d (Sw.castD₂ c (Sw.smul_dbl h) dd) := fun w₁ w₂ => H w₁ w₂

end PositivityTheory.ThKW

end
