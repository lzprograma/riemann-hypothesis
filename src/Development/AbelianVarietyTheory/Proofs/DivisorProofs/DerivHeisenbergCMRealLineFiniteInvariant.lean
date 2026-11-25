module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisDerivCM

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem map_symplOHF_eq_zero {B : Type} [CommRing B] [Algebra F B] (p : AF F →ₐ[F] B)
    (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (symplOHF σ JS JT ξ₀ x y) = 0 := by
  have h1 : p (symplOF σ JS JT ξ₀ x y) = 0 := by
    unfold symplOF hOF
    rw [GlobalTheory.WeilVacMove.sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero p σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (h.imp (fun h => ?_) fun h => ?_) <;>
    · ext i j
      exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem symplOHF_fin_real (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u v : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) (hv : v.map (finPartF F E) = 0) :
    symplOHF σ JS JT ξ₀ u v = 0 ∧ symplOHF σ JS JT ξ₀ v u = 0 :=
  ⟨Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ u v (Or.inl hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ u v (Or.inr hv)),
    Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ v u (Or.inr hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ v u (Or.inl hv))⟩

end GlobalTheory.HeisDerivCM
