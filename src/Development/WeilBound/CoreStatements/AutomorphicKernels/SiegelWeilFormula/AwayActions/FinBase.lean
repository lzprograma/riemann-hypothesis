module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def eInf : AF F := 1 - finOne F

theorem finOne_mul_eInf : finOne F * eInf F = 0 := by
  change ((0 : Ainf F) * (1 - 0), (1 : Af F) * (1 - 1)) = ((0 : Ainf F), (0 : Af F))
  simp

theorem eInf_mul_finOne : eInf F * finOne F = 0 := by
  change ((1 - 0 : Ainf F) * 0, (1 - 1 : Af F) * 1) = ((0 : Ainf F), (0 : Af F))
  simp

theorem eInf_mul_self : eInf F * eInf F = eInf F := by
  change ((1 - 0 : Ainf F) * (1 - 0), (1 - 1 : Af F) * (1 - 1)) = ((1 - 0 : Ainf F), (1 - 1 : Af F))
  simp

theorem eInf_fst_apply (w : InfinitePlace F) : (eInf F).1 w = 1 := by
  change ((1 : Ainf F) - 0) w = 1
  rw [sub_zero]
  rfl

theorem finOne_snd_mul (c : AF F) : (finOne F * c).2 = c.2 := by
  change (1 : Af F) * c.2 = c.2
  exact one_mul _

theorem finOne_fst_mul (c : AF F) : (finOne F * c).1 = 0 := by
  change (0 : Ainf F) * c.1 = 0
  exact zero_mul _

theorem eInf_fst_mul (c : AF F) : (eInf F * c).1 = c.1 := by
  change ((1 : Ainf F) - 0) * c.1 = c.1
  simp

theorem smul_split {p q : Type} (Z : Matrix p q (AE F E)) : eInf F • Z + finOne F • Z = Z := by
  rw [← add_smul, eInf, sub_add_cancel, one_smul]

end PositivityTheory.SiegelWeilFormula.KAway

end
