module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.EvXTemperate
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

theorem gs_sch {m n : ℕ} (c : ℝ) (hc : 0 < c) :
    ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, S u = gs c u := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KFock.gsSch <;> assumption

theorem schFP : SchFP := by
  intro m n c hc P
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => evX P u) S, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (PositivityTheory.SiegelWeilFormula.KMain.evX_temperate P)]
  funext u
  simp [fP, hS, smul_eq_mul]

end PositivityTheory.Rg.Sw.Glob
