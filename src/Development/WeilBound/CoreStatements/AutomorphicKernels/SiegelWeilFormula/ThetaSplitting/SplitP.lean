module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KSplitP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isPar_mul {n : ℕ} {Y : Spc F E n} {p p' : G2 σ Y} {t t' : GL (Fin n) (AE F E)} (hp : IsPar p t) (hp' : IsPar p' t') :
    IsPar (p * p') (t * t') := by
  rw [SiegelEisensteinSeries.Grp.isPar_iff] at hp hp' ⊢
  have e : mat2 (p * p') = mat2 p * mat2 p' := rfl
  rw [e, Units.val_mul, Matrix.mul_assoc, hp', ← Matrix.mul_assoc, hp, Matrix.mul_assoc]

theorem absE_pos (z : (AE F E)ˣ) : 0 < (absE F E z : ℝ) :=
  NNReal.coe_pos.2 (pos_iff_ne_zero.2 ((Group.isUnit z).map (absE F E)).ne_zero)

end PositivityTheory.SiegelWeilFormula.KSplitP

end
