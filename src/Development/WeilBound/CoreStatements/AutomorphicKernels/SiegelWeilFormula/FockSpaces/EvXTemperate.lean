module

import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest

@[expose] public section

noncomputable section

open scoped SchwartzMap
open PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

theorem evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun x : Fin m → Fin n → ℂ => evX P x) := by
  apply PositivityTheory.SiegelWeilFormula.KMain.evX_temperate

def eucl (m n : ℕ) (s : ℝ) (hs : s ≠ 0) : (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  ((LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs).trans
    ((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm)).toContinuousLinearEquiv

theorem eucl_norm_sq (m n : ℕ) (s : ℝ) (hs : s ≠ 0) (x : Fin m → Fin n → ℂ) :
    ‖eucl m n s hs x‖ ^ 2 = s ^ 2 * ∑ a, ∑ i, ‖x a i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eucl, mul_pow]

theorem gsSch (m n : ℕ) {c : ℝ} (hc : 0 < c) : ∃ G : 𝓢(Fin m → Fin n → ℂ, ℂ), ∀ x, G x = gs c x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set s := Real.sqrt (c / Real.pi) with hsdef
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (div_pos hc hpi)).ne'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eucl m n s hs)
    (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℂ (Fin m × Fin n))), fun x => ?_⟩
  have hs2 : s ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc hpi).le
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, eucl_norm_sq, gs]
  rw [hs2, Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp

end PositivityTheory.SiegelWeilFormula.KFock

end
