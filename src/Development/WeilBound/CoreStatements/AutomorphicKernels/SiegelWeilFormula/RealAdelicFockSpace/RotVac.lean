module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open Matrix

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sb (n : ℕ) (a b c e : ℂ) : M2 n := fromBlocks (a • 1) (b • 1) (c • 1) (e • 1)

theorem cs1 (t : ℝ) : (Real.cos t : ℂ) * Real.cos t + (Real.sin t : ℂ) * Real.sin t = 1 := by
  have := Real.cos_sq_add_sin_sq t
  exact_mod_cast (by nlinarith [this] : Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1)

theorem det_yrotM_ne (n : ℕ) (s : ℤˣ) (t : ℝ) : (yrotM n s t).det ≠ 0 := by
  have h := congrArg Matrix.det (_root_.PositivityTheory.SiegelWeilFormula.KFP.yrotM_mul n s t (-t))
  rw [add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.KFP.yrotM_zero, det_mul, det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem rot_unit (s : ℤˣ) (t : ℝ) (a : ℂ) (ha : a = 1 ∨ a = -1) :
    ((Real.cos t : ℂ) + a * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) ≠ 0 := by
  intro h0
  have h1 := cs1 t
  have hs := Formalism.FrobeniusOrbits.Misc2.int_units_sq_C s
  have ha2 : a * a = 1 := by rcases ha with rfl | rfl <;> ring
  have hp : ((Real.cos t : ℂ) + a * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) *
      ((Real.cos t : ℂ) - a * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) = 1 := by
    linear_combination h1 + (Real.sin t : ℂ) * Real.sin t * hs -
      ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) * (Real.sin t : ℂ) * Real.sin t * Complex.I_mul_I +
      ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) * (Real.sin t : ℂ) * Real.sin t * Complex.I * Complex.I * ha2 * (-1)
  rw [h0, zero_mul] at hp
  exact zero_ne_one hp

theorem weight_factor_rotation_ne_zero (p q : ℕ) (e : ℤ) (n : ℕ) (s : ℤˣ) (t : ℝ) : F0 p q e (yrot n s t) ≠ 0 := by
  have hu1 : u1 (yrotM n s t) = ((Real.cos t : ℂ) + (-1) * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) • 1 := by
    rw [u1, yrotM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_smul, ← add_smul]
    congr 1
    ring
  have hu2 : u2 (yrotM n s t) = ((Real.cos t : ℂ) + 1 * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) • 1 := by
    rw [u2, yrotM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_smul, ← neg_smul, ← add_smul]
    congr 1
    ring
  simp only [F0, f0, mR_yrot]
  refine mul_ne_zero (zpow_ne_zero _ (det_yrotM_ne n s t)) (mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_))
  · rw [hu1, det_smul, det_one, mul_one]
    exact pow_ne_zero _ (rot_unit s t _ (Or.inr rfl))
  · rw [hu2, det_smul, det_one, mul_one]
    exact pow_ne_zero _ (rot_unit s t _ (Or.inl rfl))

variable {d : SD σ}

end PositivityTheory.SiegelWeilFormula.KFP

end
