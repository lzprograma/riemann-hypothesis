module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.RawLift.Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem hO_eq_trace (x y : WO V W) :
    hO V W x y = Matrix.trace ((V.gram⁻¹).map (incA D) * ((y.map (cA D))ᵀ * W.gram.map (incA D) * x)) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem hO_ratMul (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (u v : WO V W) :
    hO V W (ratMul C u) (ratMul C v) =
      Matrix.trace ((V.gram⁻¹).map (incA D) * ((v.map (cA D))ᵀ * (Cᴴ * W.gram * C).map (incA D) * u)) := by
  have h : (C.map (incA D)).map (cA D) = (Cᴴ.map (incA D))ᵀ := by
    ext i j; simp [Matrix.map_apply, _root_.GlobalTheory.DualPairCheck.cA_incA]
  rw [hO_eq_trace]
  unfold ratMul
  rw [Matrix.map_mul, h, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem gram_eq {Y : Lag W} {C} (h : IsLagFrame W Y C) : C.1ᴴ * W.gram * C.1 = C.2ᴴ * W.gram * C.2 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  funext j k
  have m : ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 := fun j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  have := Y.2.2 _ (m j) _ (m k)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply] at this
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using this

theorem ratMul_add (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (γ) (u : WO V W) :
    ratMul C (ratW W V γ + u) = ratW W V (C * γ) + ratMul C u := by
  unfold ratMul ratW
  rw [Matrix.mul_add, Matrix.map_mul]

theorem integrand_periodic (hψ : ∀ x, ‖ψ x‖ = 1) {Y : Lag W} {C} (h : IsLagFrame W Y C) {f₁ f₂ : WO V W → ℂ}
    (h₁ : IsThetaFunO ψ V W f₁) (h₂ : IsThetaFunO ψ V W f₂) (γ) (u : WO V W) :
    f₁ (ratMul C.1 (ratW W V γ + u)) * star (f₂ (ratMul C.2 (ratW W V γ + u))) =
      f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
  have e : ∀ B : Matrix (Fin W.rank) (Fin W.rank) D.host.E, ratW W V (B * γ) = ratMul B (ratW W V γ) := fun B => by
    unfold ratMul ratW; rw [Matrix.map_mul]
  have s : symplOH V W (ratW W V (C.1 * γ)) (ratMul C.1 u) = symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u) := by
    rw [e, e]; unfold symplOH symplO; rw [hO_ratMul, hO_ratMul, gram_eq h]
  rw [ratMul_add, ratMul_add, h₁.quasi, h₂.quasi, s, star_mul']
  set z := ψ (-(symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u))) with hz
  have : z * star z = 1 := by
    have := Complex.mul_conj' z
    rw [hz, hψ] at this
    simpa using this
  calc _ = (z * star z) * (f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) := by ring
    _ = _ := by rw [this, one_mul]

end GlobalTheory.RawLift.Model

end
