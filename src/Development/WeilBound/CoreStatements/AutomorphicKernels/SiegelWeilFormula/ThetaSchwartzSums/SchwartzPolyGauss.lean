module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzPolyMulGauss

@[expose] public section

noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.SiegelWeilFormula.KMain

open PositivityTheory.Rg.Sw

def coordX {m n : ℕ} (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

theorem coordX_temperate {m n : ℕ} (k : Fin m × Fin n × Bool) : Function.HasTemperateGrowth (coordX k) := by
  apply _root_.GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord_temperate <;> assumption

theorem evX_temperate {m n : ℕ} (P : PX m n) : Function.HasTemperateGrowth (fun x => evX P x) := by
  have hev : (fun x => evX P x) = fun x => MvPolynomial.eval (fun k => coordX k x) P := by
    funext x
    rfl
  rw [hev]
  induction P using MvPolynomial.induction_on with
  | C c0 =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const c0
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact Function.HasTemperateGrowth.add (hp rfl) (hq rfl)
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact Function.HasTemperateGrowth.mul (hp rfl) (coordX_temperate k)

end PositivityTheory.SiegelWeilFormula.KMain

end
