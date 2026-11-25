module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.EtaCMType

theorem idFF_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : Fˣ) :
    idFF F E (Units.map (algebraMap F (AF F)).toMonoidHom a) =
      Units.map (incAF F E).toMonoidHom (Units.map (algebraMap F E).toMonoidHom a) := by
  apply Units.ext
  change algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (a : F)) =
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E (a : F))
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem continuous_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Continuous (idFF F E) := by
  haveI := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E)))

theorem at_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : (AF F)ˣ)
    (h : At (evI F) ((a : AF F) - 1)) :
    At (evI F) (((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := by
  intro u hu
  have e : ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = algebraMap (AF F) (AF F ⊗[F] E) ((a : AF F) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [e, Algebra.smul_def, ← map_mul, ← smul_eq_mul, h u hu, map_zero]

end GlobalTheory.EtaCMType
