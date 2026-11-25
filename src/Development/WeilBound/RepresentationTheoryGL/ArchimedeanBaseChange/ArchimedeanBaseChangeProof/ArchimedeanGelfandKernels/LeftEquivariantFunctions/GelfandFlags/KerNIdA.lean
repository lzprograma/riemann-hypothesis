module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevel
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.SecondCountableG

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

theorem memGL (y : G n) : y.val ∈ GLs n := PositivityTheory.RgBcC.VC.NAvgH.mem_GLsG y

def S2 (a : Mat n) : ℝ := ∑ i, ∑ j, ‖a i j‖ ^ 2

theorem schatten_two_nonneg (a : Mat n) : 0 ≤ S2 a := by
  unfold S2
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

theorem schatten_two_mul_le (a b : Mat n) : S2 (a * b) ≤ S2 a * S2 b := by
  apply _root_.PositivityTheory.RgBcC.VC.NAvgH.sq_mul_le <;> assumption

theorem lg_eq (y : Mat n) : lg y = Real.log (1 + S2 y + S2 y⁻¹) := by
  unfold lg S2
  congr 1
  simp only [Finset.sum_add_distrib]
  ring

theorem lg_mul_le (a b : Mat n) : lg (a * b) ≤ lg a + lg b := by
  apply _root_.PositivityTheory.RgBcC.VC.NAvgH.lg_mul_le <;> assumption

theorem lg_inv (a : Mat n) (ha : a ∈ GLs n) : lg a⁻¹ = lg a := by
  exact PositivityTheory.RgBcC.VC.NAvgH.lg_inv a ha

theorem lg_le_of_mul (u y : Mat n) (hy : y ∈ GLs n) : lg u ≤ lg (u * y) + lg y := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have e : u = u * y * y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc lg u = lg (u * y * y⁻¹) := congrArg lg e
    _ ≤ lg (u * y) + lg y⁻¹ := lg_mul_le _ _
    _ = lg (u * y) + lg y := by rw [lg_inv y hy]

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem lg_contOn : ContinuousOn lg (GLs n) := by
  apply _root_.GlobalTheory.CompanionTheory.SobGL.continuousOn_lg <;> assumption

end PositivityTheory.RgBcC.VC.KN
