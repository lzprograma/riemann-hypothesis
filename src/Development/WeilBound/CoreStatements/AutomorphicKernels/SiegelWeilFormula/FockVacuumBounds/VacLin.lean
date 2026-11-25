module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cosetSum_const_mul {G : Type} [Group G] (Pp Γ : Subgroup G) (a : ℂ) (f : G → ℂ) (g : G) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun y => a * f y) g = a * GlobalTheory.Eis.cosetSum Pp Γ f g := by
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
  exact tsum_mul_left

end PositivityTheory.SiegelWeilFormula.Atop

end
