module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

@[expose] public section

noncomputable section

namespace PI.EF

open Complex Filter Set

theorem norm_Gamma_le {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp

end PI.EF
