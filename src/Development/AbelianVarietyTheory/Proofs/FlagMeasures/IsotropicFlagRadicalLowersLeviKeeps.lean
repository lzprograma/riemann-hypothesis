module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagMem

variable {n : ℕ} {ε : Fin n → Bool}

theorem form_mul (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star (uMat g⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simpa using GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y

theorem Jm_mul_self : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε

theorem Jm_mul_conjTranspose (m : Formalism.REAL.UJ ε) :
    Formalism.REAL.Jm ε * (uMat m)ᴴ = uMat m⁻¹ * Formalism.REAL.Jm ε := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, GlobalTheory.FlagLeviGroup.uMat_mul_inv, Matrix.mul_one]
  calc Formalism.REAL.Jm ε * (uMat m)ᴴ
      = Formalism.REAL.Jm ε * ((uMat m)ᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = _ := by rw [← h1, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem form_conjTranspose (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat m)ᴴ *ᵥ y)) = star ((uMat m⁻¹)ᴴ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Jm_mul_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧
      ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  intro n ε a j W hW
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).1
    have hu' : u⁻¹ ∈ flagN ε W := by
      rw [← hN] at hu ⊢
      exact N.inv_mem hu
    simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into, Matrix.sub_mulVec, Matrix.one_mulVec]
    refine ⟨⟨hu.1, hu.2⟩, fun i y hy x hx => ?_⟩
    have h := hy _ (hu'.1 i x hx)
    rw [star_sub, sub_dotProduct] at h
    rw [Matrix.mulVec_sub, dotProduct_sub, form_mul]
    exact h
  · have hm' : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub (ε := ε) W).inv_mem hm
    simp only [GlobalTheory.IwConst.keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]
    refine ⟨⟨fun i y hy => (hm i y hy).1, fun i y hy x hx => ?_⟩,
      ⟨fun i y hy => (hm i y hy).2, fun i y hy x hx => ?_⟩⟩
    · rw [form_mul]
      exact hy _ (hm' i x hx).1
    · rw [form_conjTranspose]
      exact hy _ (hm' i x hx).2

end GlobalTheory.IwConst.FlagMem
