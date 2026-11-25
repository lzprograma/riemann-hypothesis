module

public import Formalism.RealPlaceAnalysis.StatementC
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds
public import Formalism.RealPlaceAnalysis.StatementA
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasComm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId, Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds, Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

-- ===== clump member: Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId =====
-- clump-header: {"m": "Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.StatementC\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Finset Polynomial

noncomputable section

namespace Formalism.REAL

end Formalism.REAL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId =====

-- ===== clump member: Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds =====
-- clump-header: {"m": "Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.StatementA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Finset

noncomputable section

namespace Formalism.REAL

theorem iteratedGrowthBound_holds : GrowthIter := by
  intro V _ _ X U B C hB hC hX j k
  induction k generalizing j with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    obtain ⟨hXw, hnorm⟩ := hX j w hw
    have h1 := ih (j + 1) (X w) hXw
    have e : B + ((j + 1 : ℕ) : ℝ) + (k : ℝ) = B + (j : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
    rw [e] at h1
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hBj : 0 ≤ B + (j : ℝ) := by linarith
    have hL : 0 ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hBjL : B + (j : ℝ) ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hCk : 0 ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k := by positivity
    calc ‖(X ^ (k + 1)) w‖ = ‖(X ^ k) (X w)‖ := by rw [pow_succ, Module.End.mul_apply]
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * ‖X w‖ := h1
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * (C * (B + j) * ‖w‖) := by gcongr
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k *
            (C * (B + (j : ℝ) + ((k : ℝ) + 1)) * ‖w‖) := by gcongr
      _ = C ^ (k + 1) * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ (k + 1) * ‖w‖ := by ring

theorem taylorSummable_holds : TaylorRadius := by
  intro C m t hC hm ht h
  have hCt : 0 ≤ C * t := mul_nonneg hC ht
  have hr0 : 0 ≤ C * t * Real.exp 1 := by positivity
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 h).mul_left (Real.exp m))
  have hx : 0 ≤ m + (k : ℝ) := by positivity
  have h1 := Real.pow_div_factorial_le_exp (m + k) hx k
  have h2 : Real.exp (m + k) = Real.exp m * Real.exp 1 ^ k := by
    rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
  have hCtk : 0 ≤ (C * t) ^ k := pow_nonneg hCt k
  calc (C * t) ^ k * (m + k) ^ k / (k.factorial : ℝ)
      = (C * t) ^ k * ((m + k) ^ k / (k.factorial : ℝ)) := by ring
    _ ≤ (C * t) ^ k * Real.exp (m + k) := by gcongr
    _ = Real.exp m * (C * t * Real.exp 1) ^ k := by rw [h2]; ring

end Formalism.REAL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds =====

-- ===== clump member: Formalism.RealPlaceAnalysis.ThirdArithmeticHolds =====
-- clump-header: {"m": "Formalism.RealPlaceAnalysis.ThirdArithmeticHolds", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.StatementC\npublic import Formalism.RealPlaceAnalysis.StatementE\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasComm\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet\nimport Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard\nimport Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds\nimport Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.REAL

theorem wdCas : WDCas := by
  intro V _ _ n ε E μ w hGl hU hKH
  have hK := compactCasimirOnHighestWeight_holds V n ε E μ w hGl hKH
  have hU' : IsUnitary ε (fun a b => if ε a = ε b then E a b else 0) := by
    intro a b x y
    by_cases h : ε a = ε b
    · simp only [ite_eq_left h, ite_eq_left h.symm]
      exact hU a b x y
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp only [ite_eq_right h, ite_eq_right h', LinearMap.zero_apply, inner_zero_left, inner_zero_right,
        mul_zero]
  have hCas' : Cas (fun a b => if ε a = ε b then E a b else 0) = CasK ε E := by
    unfold Cas CasK
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : ε a = ε b
    · simp only [ite_eq_left h, ite_eq_left h.symm]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp only [ite_eq_right h, ite_eq_right h', zero_mul]
  have hCasK' : CasK ε (fun a b => if ε a = ε b then E a b else 0) = CasK ε E := by
    unfold CasK
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : ε a = ε b
    · simp only [ite_eq_left h, ite_eq_left h.symm]
    · simp only [ite_eq_right h]
  have hS : (∑ a, ∑ b, ‖E a b w‖ ^ 2) =
      (∑ a, ∑ b, ‖(if ε a = ε b then E a b else 0) w‖ ^ 2) +
        ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b w‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : ε a = ε b <;> simp [h]
  have hSc := congrArg (fun r : ℝ => (r : ℂ)) hS
  have h1 := sumOfSquaresIdentity_holds V n ε E w hU
  have h2 := sumOfSquaresIdentity_holds V n ε (fun a b => if ε a = ε b then E a b else 0) w hU'
  rw [hCas', hCasK'] at h2
  first | rw [two_nsmul] at h1 h2
  rw [add_sub_cancel_right, hK, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  rw [LinearMap.sub_apply, LinearMap.add_apply, inner_sub_right, inner_add_right, hK,
    inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  push_cast at h1 h2 hSc ⊢
  linear_combination h1 - hSc - h2
alias rhoStd := _root_.Formalism.REAL.half_sum_roots_standard

theorem growthIter : GrowthIter := iteratedGrowthBound_holds
theorem taylorRadius : TaylorRadius := taylorSummable_holds
alias casCentral := _root_.Formalism.REAL.casimir_central_holds

end Formalism.REAL

namespace Formalism.REAL
end Formalism.REAL

namespace Formalism.REAL
end Formalism.REAL

namespace Formalism.REAL
theorem qSkewRow : QSkewRow := quantumMinorRowSkew_holds
theorem qSkewCol : QSkewCol := quantumMinorColSkew_holds
theorem qDetHW : QDetHW := quantumDetHighestWeight_holds
theorem qDetCentral : QDetCentral := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
theorem qComatrix : QComatrix := qComatrix_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
end Formalism.REAL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.RealPlaceAnalysis.ThirdArithmeticHolds =====
