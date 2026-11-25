module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffDerivHeisenbergCMRealLineTheta
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisLineDiffF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAEF : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAEF : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_AF (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add (f := _), LinearMap.map_add (f := _), ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem map_trace_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (p : R →ₐ[F] R')
    (y : R ⊗[F] E) :
    p (Algebra.trace R (R ⊗[F] E) y) =
      Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) y) := by
  have h1 : ∀ (S : Type) [CommRing S] [Algebra F S] (r : S) (x : E),
      Algebra.trace S (S ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F S (Algebra.trace F E x) := by
    intro S _ _ r x
    have h1 : Algebra.trace S (S ⊗[F] E) ((1 : S) ⊗ₜ[F] x) = algebraMap F S (Algebra.trace F E x) := by
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    have h2 : r ⊗ₜ[F] x = r • ((1 : S) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2, LinearMap.map_smul, h1, smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h1, h1, map_mul, AlgHom.commutes]
  | add y y' hy hy' => simp only [map_add (f := _), hy, hy']

theorem finPartF_sigR (σ : E →ₐ[F] E) (z : AEF F E) :
    finPartF F E (sigR (AF F) σ z) = sigR (Af F) σ (finPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

theorem sndA_symplOHF (ξ₀ : E) (w y : WOF F E nS nT) (hy : y.map (finPartF F E) = 0) :
    sndA F (symplOHF σ JS JT ξ₀ w y) = 0 := by
  apply _root_.GlobalTheory.ThetaLineSmoothF.snd_symplOHF <;> assumption

theorem symplOHF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOHF_zero_right (ξ₀ : E) (x : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x 0 = 0 := by
  have := symplOHF_add_right σ JS JT ξ₀ x 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem continuous_symplOHF (ξ₀ : E) (w : WOF F E nS nT) {X : Type} [TopologicalSpace X] {y : X → WOF F E nS nT}
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ₀ w (y t) := by
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    (continuous_sigR_AF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hh : Continuous fun t => hOF σ JS JT w (y t) :=
    continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul continuous_const
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

theorem exists_log {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStdCharF tauE ψ (-1)) :
    ∃ lam : AF F →+ ℂ, Continuous lam ∧ ∀ a, sndA F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (fstA F a ⊗ₜ[F] (1 : E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finsetSum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA F a)
    have e : pairA F (fstA F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

end GlobalTheory.HeisLineDiffF

