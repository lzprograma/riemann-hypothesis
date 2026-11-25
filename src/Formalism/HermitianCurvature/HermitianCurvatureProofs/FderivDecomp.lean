module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)

def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)

def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}

theorem normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by

  first
    | rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem isOpen_Hh (TT : ℝ) : IsOpen (Hh TT) := isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)

theorem convex_Hh (TT : ℝ) : Convex ℝ (Hh TT) := by
  have hmono : Monotone (fun x : ℝ => Real.exp x ^ 2) := fun _ _ h =>
    pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr h) 2
  simpa [Hh, normSq_exp] using (hmono.convex_gt TT).linear_preimage Complex.reLm

def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w

def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

theorem omL_apply (c v : ℂ) : omL c v = 2 * (c * v).im := by

  simp [omL]

def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)

theorem om_apply (α : ℂ → ℂ) (w v : ℂ) : om α w v = 2 * (bet α w * v).im := omL_apply _ _

theorem bet_periodic (α : ℂ → ℂ) (w : ℂ) (k : ℤ) : bet α (w + (k : ℂ) * (2 * Real.pi * I)) = bet α w := by

  simp only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
