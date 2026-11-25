module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Glue

variable (d : SD σ)

variable {p : Type} [Fintype p] [DecidableEq p]


open Classical in
def fam (w : InfinitePlace F) (Z : Matrix p p ℂ) (w' : InfinitePlace F) : Matrix p p ℂ := if w' = w then Z else 1

theorem fin_idem : finOne F * finOne F = finOne F := by
  show ((0 : Ainf F), (1 : Af F)) * ((0 : Ainf F), (1 : Af F)) = ((0 : Ainf F), (1 : Af F))
  rw [Prod.mk_mul_mk, mul_zero, mul_one]

theorem fin_mul {q : Type} [Fintype q] (A B : Matrix q q (AE F E)) :
    finOne F • (A * B) = (finOne F • A) * (finOne F • B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, fin_idem]

end Glue

section Iota

variable (d : SD σ)

theorem incM_one {p : Type} [DecidableEq p] : incM F (1 : Matrix p p E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem conj_unit {ι : Type} [Fintype ι] [DecidableEq ι] (b bi Z D Q : Matrix ι ι ℂ) (hb : b * bi = 1)
    (hQ : bᵀ * D * b.map star = Q) (hZ : Zᵀ * Q * Z.map star = Q) : (b * Z * bi)ᵀ * D * (b * Z * bi).map star = D := by
  have hD : D = biᵀ * Q * bi.map star := by
    calc D = (b * bi)ᵀ * D * (b * bi).map star := by
          rw [hb, Matrix.transpose_one, mapStar_one, Matrix.one_mul, Matrix.mul_one]
      _ = biᵀ * (bᵀ * D * b.map star) * bi.map star := by
          rw [Matrix.transpose_mul, mapStar_mul]; simp only [Matrix.mul_assoc]
      _ = biᵀ * Q * bi.map star := by rw [hQ]
  calc (b * Z * bi)ᵀ * D * (b * Z * bi).map star = biᵀ * (Zᵀ * (bᵀ * D * b.map star) * Z.map star) * bi.map star := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, mapStar_mul, mapStar_mul]; simp only [Matrix.mul_assoc]
    _ = D := by rw [hQ, hZ, ← hD]

theorem map_cA_smul {p q : Type} (a : AF F) (A : Matrix p q (AE F E)) : (a • A).map (cA σ) = a • A.map (cA σ) := by
  ext i j
  exact map_smul (cA σ) a (A i j)

end Iota

end PositivityTheory.SiegelWeilFormula.Krd

end
