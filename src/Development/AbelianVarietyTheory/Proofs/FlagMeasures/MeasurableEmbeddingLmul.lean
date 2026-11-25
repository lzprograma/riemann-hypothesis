module

import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AbsOfRange
public import Formalism.PeriodIntegrals.BesselMapUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchur

theorem fdegHC_pos {n : ℕ} {mu : Fin n → ℝ} (h : StrictAnti mu) : 0 < Formalism.QuantumDeterminants.fdegHC mu := by
  unfold Formalism.QuantumDeterminants.fdegHC
  refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
  · have := h (Finset.mem_filter.1 hb).2
    exact abs_pos.2 (sub_ne_zero.2 this.ne')
  · have : (a : ℕ) < b := (Finset.mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
    linarith

theorem measurableEmbedding_lmul {k r : ℕ} {t : MatKR k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (fun x : Mt k r => (fun i j => (t⁻¹ * Matrix.of x) i j : Mt k r)) := by
  have hc : ∀ s : MatKR k r, Continuous (fun x : Mt k r => (fun i j => (s * Matrix.of x) i j : Mt k r)) := fun s => by
    have h1 : Continuous (fun x : Mt k r => (Matrix.of x : MatKR k r)) := continuous_id
    exact continuous_const.matrix_mul h1
  let e : Mt k r ≃ᵐ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => by
        show t * (t⁻¹ * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
      right_inv := fun x => by
        show t⁻¹ * (t * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
      measurable_toFun := (hc _).measurable
      measurable_invFun := (hc _).measurable }
  exact e.measurableEmbedding

theorem isBesselMapSm_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp} (h : IsBesselMapSm z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW σ w v := fun w v => by
    induction w with
    | nil => rfl
    | cons X w ih => exact congrArg (dsig σ X) ih
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simpa only [e] using h5 v hv

theorem theta_pos (D : D7) {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hv : 0 ≤ D.host.v) (hW : GoodW D τ w w' θ W) : 0 < θ := by
  apply _root_.GlobalTheory.Amp.RangeModel.theta_pos <;> assumption

end GlobalTheory.BesselSchur
