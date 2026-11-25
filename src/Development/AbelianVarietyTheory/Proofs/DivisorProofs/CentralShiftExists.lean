module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.CentralShift

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

theorem glued_idempotent_units_mul_eq_one {e e' a ai b bi : A} (h1 : e * e = e) (h2 : e * e' = 0) (h3 : e' * e' = e') (ha : a * ai = 1)
    (hb : b * bi = 1) : (e * a + e' * bi + (1 - e - e')) * (e' * b + e * ai + (1 - e - e')) = 1 := by
  linear_combination (a * ai - a - ai + 1) * h1 + (a * b + bi * ai - a - bi - b - ai + 2) * h2 +
    (bi * b - bi - b + 1) * h3 + e * ha + e' * hb

def scal (n : ℕ) {u v : A} (h : u * v = 1) : GL (Fin n) A where
  val := u • (1 : Matrix (Fin n) (Fin n) A)
  inv := v • (1 : Matrix (Fin n) (Fin n) A)
  val_inv := by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, one_smul, one_mul]
  inv_val := by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm v, h, one_smul, one_mul]

end Generic

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end Frame

section Adelic

open GlobalTheory.LevSplit

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E)) (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ Lev.IsConjPl Q Q') :
    ∃ e : Formalism.L2.Theta.AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')

end Adelic

theorem inner_eq_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →ₗ[ℂ] H)
    (h : ∀ x, ‖T x‖ = ‖x‖) (y y' : H) : ⟪T y, T y'⟫_ℂ = ⟪y, y'⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨T, h⟩ y y'

end GlobalTheory.CentralShift

end
