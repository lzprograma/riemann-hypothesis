module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ExistsNeZeroOfMap
import Mathlib.Tactic.Linter.Style
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp

namespace PositivityTheory.SiegelWeilFormula.MeasD

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigR_eq (z : AF F ⊗[F] E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem incM_scalar_mul {k p : ℕ} (η : E) (M : Matrix (Fin k) (Fin p) (AE F E)) :
    incM F (Matrix.scalar (Fin k) η) * M = inclR (F := F) (AF F) η • M := by
  rw [Matrix.smul_eq_diagonal_mul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [incM, Matrix.scalar_apply, h]

theorem inclR_inv_mul {η : E} (hne : η ≠ 0) : inclR (F := F) (AF F) η⁻¹ * inclR (F := F) (AF F) η = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hne, map_one]

end PositivityTheory.SiegelWeilFormula.MeasD

end
