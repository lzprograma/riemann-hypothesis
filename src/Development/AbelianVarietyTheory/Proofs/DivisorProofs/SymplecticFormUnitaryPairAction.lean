module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology

namespace GlobalTheory.SymplOInv

private theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A)
    (P : Matrix (Fin n) (Fin n) A) (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P * P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  have h1 : (P * (k.map σ)ᵀ * P') * k = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc P, hk, hP]
  have h2 : k * (P * (k.map σ)ᵀ * P') = 1 := mul_eq_one_comm.1 h1
  have hP' : P' * P = 1 := mul_eq_one_comm.1 hP
  have hk' : k * P * (k.map σ)ᵀ = P := by
    calc k * P * (k.map σ)ᵀ = k * P * (k.map σ)ᵀ * (P' * P) := by rw [hP', Matrix.mul_one]
      _ = (k * (P * (k.map σ)ᵀ * P')) * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [h2, Matrix.one_mul]
  have e : P * ((g * y * k).map σ)ᵀ * Q * (g * x * k) =
      (P * (k.map σ)ᵀ * ((y.map σ)ᵀ * ((g.map σ)ᵀ * Q * g) * x)) * k := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [sum_four_eq_trace, sum_four_eq_trace, e, hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc k, hk']
  simp only [Matrix.mul_assoc]

theorem hO_actO {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    hO S T (actO S T g h x) (actO S T g h y) = hO S T x y := by
  have h1 : S.gram⁻¹.map (incA D) * S.gram.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (incA D).map_zero (incA D).map_one
  exact sum_unitary (cA D) (T.gram.map (incA D)) (mt T h) (S.gram⁻¹.map (incA D)) (S.gram.map (incA D)) (mt S g⁻¹)
    h1 h.2 (g⁻¹).2 x y

theorem symplO_actO : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  intro D S T g h x y
  unfold symplO
  rw [hO_actO]

end GlobalTheory.SymplOInv
