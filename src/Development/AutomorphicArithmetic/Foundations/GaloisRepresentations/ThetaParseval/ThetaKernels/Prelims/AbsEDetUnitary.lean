module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.GroupWithZero.Basic

@[expose] public section

open scoped NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Doubling

namespace GlobalTheory.WeilEx.Jac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/-- The determinant of an adelic unitary matrix has norm one. -/
theorem absE_det_unitary {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det g.1) = 1 := by
  have hunit : IsUnit (incM F J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.isUnit.map _
  have hdet := congrArg Matrix.det
    (show (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, hunit.mul_eq_right,
    show ((mat g).map (cA σ)).det = sigR (AF F) σ (mat g).det from
      (RingHom.map_det (sigR (AF F) σ) _).symm] at hdet
  have hconj : Matrix.GeneralLinearGroup.det g.1 * conjUnit σ (Matrix.GeneralLinearGroup.det g.1) = 1 :=
    Units.ext hdet
  have hnorm := congrArg (absE F E) hconj
  rw [map_mul, absE_conjUnit, map_one] at hnorm
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, hnorm])

end GlobalTheory.WeilEx.Jac
