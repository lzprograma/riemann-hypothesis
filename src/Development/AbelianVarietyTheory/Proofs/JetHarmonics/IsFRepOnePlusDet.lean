module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace BranchingSupport.TensInh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

open scoped Matrix.Norms.Elementwise

variable {k r : ℕ}

theorem lenA_eq_lA (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin (r + 1)) :
    lenA k r z g a = Formalism.MainNotions.S.lA k r z g a := by
  classical
  let Lm : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    { toFun := fun v => WithLp.toLp 2 (g⁻¹ *ᵥ v)
      map_add' := fun v w => by simp [Matrix.mulVec_add]
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }
  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ
    (Set.range fun b : {b : Fin r // b.val < a.val} => Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1))
  have hlt : ∀ b : Fin (r + 1), b < a → b.val < r :=
    fun b hb => Nat.lt_of_lt_of_le hb (Nat.le_of_lt_succ a.2)
  have hfv : ∀ (b : Fin (r + 1)) (hb : b < a),
      Formalism.QuantumDeterminants.fvec k r z b = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r ⟨b.val, hlt b hb⟩) := by
    intro b hb
    have hbr : b.val < r := hlt b hb
    simp [Formalism.QuantumDeterminants.fvec, hbr]
  have hspan : Submodule.span ℂ ((fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) '' {b | b < a}) = S.map Lm := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨_, ⟨⟨⟨b.val, hlt b hb⟩, hb⟩, rfl⟩, ?_⟩
      exact (congrArg (fun v => (WithLp.toLp 2 (g⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin (2 * r + k + 1))))
        (hfv b hb)).symm
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      refine ⟨⟨b.val, by have := b.2; omega⟩, hb, ?_⟩
      show WithLp.toLp 2 (g⁻¹ *ᵥ _) = _
      rw [hfv _ hb]
      rfl
  have hd : ∀ y, dist (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))
      (WithLp.toLp 2 (g⁻¹ *ᵥ y)) = Formalism.MainNotions.S.eucl (g⁻¹ *ᵥ (Formalism.QuantumDeterminants.fvec k r z a - y)) := by
    intro y
    rw [EuclideanSpace.dist_eq]
    simp [Formalism.MainNotions.S.eucl, Matrix.mulVec_sub, Complex.normSq_eq_norm_sq, dist_eq_norm]
  unfold lenA Formalism.MainNotions.S.lA
  rw [hspan, Metric.infDist_eq_iInf, ← sInf_range]
  congr 1
  ext t
  constructor
  · rintro ⟨⟨_, y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, hd y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨Lm y, y, hy, rfl⟩, hd y⟩

end BranchingSupport.TensInh
