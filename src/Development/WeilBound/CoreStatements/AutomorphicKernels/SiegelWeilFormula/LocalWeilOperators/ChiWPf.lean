module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace KC

variable (d : SD σ)

theorem finOne_mul_self : finOne F * finOne F = finOne F := by
  first
  | (show ((0 : Ainf F), (1 : Af F)) * ((0 : Ainf F), (1 : Af F)) = ((0 : Ainf F), (1 : Af F)); simp)

theorem e_mul_e : (finOne F • (1 : AE F E)) * (finOne F • (1 : AE F E)) = finOne F • (1 : AE F E) := by
  rw [smul_mul_assoc, one_mul, smul_smul, finOne_mul_self]

theorem update_mul (w : InfinitePlace F) (z z' : ℂ) :
    Function.update (fun _ => (1 : ℂ)) w (z * z') =
      Function.update (fun _ => (1 : ℂ)) w z * Function.update (fun _ => (1 : ℂ)) w z' := by
  funext v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

end KC

end PositivityTheory.SiegelWeilFormula

end
