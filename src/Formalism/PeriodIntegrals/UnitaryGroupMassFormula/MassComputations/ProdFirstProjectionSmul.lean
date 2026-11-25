module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace MassDataMassesW.SplitW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]

abbrev q1 : (R1 × R2) ⊗[F] E →+* R1 ⊗[F] E := tensMap (E := E) (AlgHom.fst F R1 R2)

abbrev q2 : (R1 × R2) ⊗[F] E →+* R2 ⊗[F] E := tensMap (E := E) (AlgHom.snd F R1 R2)

def qq : (R1 × R2) ⊗[F] E →+* (R1 ⊗[F] E) × (R2 ⊗[F] E) := RingHom.prod (q1 R1 R2) (q2 R1 R2)

theorem prodFirstProjection_smul (c : R1 × R2) (z : (R1 × R2) ⊗[F] E) : q1 R1 R2 (c • z) = c.1 • q1 R1 R2 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [tensMap, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem second_factor_proj_smul (c : R1 × R2) (z : (R1 × R2) ⊗[F] E) : q2 R1 R2 (c • z) = c.2 • q2 R1 R2 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [tensMap, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem prodLeft_apply (z : (R1 × R2) ⊗[F] E) :
    TensorProduct.prodLeft F F R1 R2 E z = qq R1 R2 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.prodLeft_tmul]
    simp [qq, tensMap]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem qq_bijective : Function.Bijective (qq (F := F) (E := E) R1 R2) := by
  have h : (qq (F := F) (E := E) R1 R2 : (R1 × R2) ⊗[F] E → (R1 ⊗[F] E) × (R2 ⊗[F] E)) =
      TensorProduct.prodLeft F F R1 R2 E := funext fun z => (prodLeft_apply R1 R2 z).symm
  rw [h]
  exact (TensorProduct.prodLeft F F R1 R2 E).bijective

def QQ : (R1 × R2) ⊗[F] E ≃+* (R1 ⊗[F] E) × (R2 ⊗[F] E) := RingEquiv.ofBijective _ (qq_bijective R1 R2)

theorem QQ_apply (z : (R1 × R2) ⊗[F] E) : QQ R1 R2 z = (q1 R1 R2 z, q2 R1 R2 z) := by
  rfl

theorem first_factor_proj_equiv_symm (p : (R1 ⊗[F] E) × (R2 ⊗[F] E)) : q1 R1 R2 ((QQ R1 R2).symm p) = p.1 := by
  simpa only [QQ_apply] using congrArg Prod.fst (RingEquiv.apply_symm_apply (QQ R1 R2) p)

theorem second_factor_proj_equiv_symm (p : (R1 ⊗[F] E) × (R2 ⊗[F] E)) : q2 R1 R2 ((QQ R1 R2).symm p) = p.2 := by
  simpa only [QQ_apply] using congrArg Prod.snd (RingEquiv.apply_symm_apply (QQ R1 R2) p)

def j1 (x : R1 ⊗[F] E) : (R1 × R2) ⊗[F] E := (QQ R1 R2).symm (x, 0)

def j2 (y : R2 ⊗[F] E) : (R1 × R2) ⊗[F] E := (QQ R1 R2).symm (0, y)

theorem first_factor_incl_smul (a : R1) (x : R1 ⊗[F] E) :
    j1 R1 R2 (a • x) = ((a, 1) : R1 × R2) • j1 R1 R2 x := by
  apply (QQ R1 R2).injective
  rw [QQ_apply, QQ_apply, prodFirstProjection_smul, second_factor_proj_smul]
  simp only [j1, first_factor_proj_equiv_symm, second_factor_proj_equiv_symm, smul_zero]

theorem second_factor_incl_smul (b : R2) (y : R2 ⊗[F] E) :
    j2 R1 R2 (b • y) = ((1, b) : R1 × R2) • j2 R1 R2 y := by
  apply (QQ R1 R2).injective
  rw [QQ_apply, QQ_apply, prodFirstProjection_smul, second_factor_proj_smul]
  simp only [j2, first_factor_proj_equiv_symm, second_factor_proj_equiv_symm, smul_zero]

theorem QQ_symm_eq_add (p : (R1 ⊗[F] E) × (R2 ⊗[F] E)) :
    (QQ R1 R2).symm p = j1 R1 R2 p.1 + j2 R1 R2 p.2 := by
  rw [j1, j2, ← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add]

section Top

variable [TopologicalSpace R1] [TopologicalSpace R2]

instance isModTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

instance ctsSMulTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    ContinuousSMul R (R ⊗[F] E) := ModuleTopology.continuousSMul R (R ⊗[F] E)

instance ctsAddTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    ContinuousAdd (R ⊗[F] E) := ModuleTopology.continuousAdd R (R ⊗[F] E)

theorem continuous_first_factor_proj : Continuous (q1 (F := F) (E := E) R1 R2) :=
  IsModuleTopology.continuous_of_distribMulActionHomₑ
    (σ := MonoidHom.fst R1 R2) continuous_fst
    { toAddMonoidHom := (q1 (F := F) (E := E) R1 R2).toAddMonoidHom
      map_smul' := prodFirstProjection_smul R1 R2 }

theorem continuous_second_factor_proj : Continuous (q2 (F := F) (E := E) R1 R2) :=
  IsModuleTopology.continuous_of_distribMulActionHomₑ
    (σ := MonoidHom.snd R1 R2) continuous_snd
    { toAddMonoidHom := (q2 (F := F) (E := E) R1 R2).toAddMonoidHom
      map_smul' := second_factor_proj_smul R1 R2 }

theorem continuous_first_factor_incl : Continuous (j1 (F := F) (E := E) R1 R2) :=
  IsModuleTopology.continuous_of_distribMulActionHomₑ
    (σ := MonoidHom.inl R1 R2) (continuous_id.prodMk continuous_const)
    { toAddMonoidHom := AddMonoidHom.mk' (j1 (F := F) (E := E) R1 R2) fun x y => by
        rw [j1, j1, j1, ← map_add (f := _), Prod.mk_add_mk, add_zero]
      map_smul' := first_factor_incl_smul R1 R2 }

theorem continuous_second_factor_incl : Continuous (j2 (F := F) (E := E) R1 R2) :=
  IsModuleTopology.continuous_of_distribMulActionHomₑ
    (σ := MonoidHom.inr R1 R2) (continuous_const.prodMk continuous_id)
    { toAddMonoidHom := AddMonoidHom.mk' (j2 (F := F) (E := E) R1 R2) fun x y => by
        rw [j2, j2, j2, ← map_add (f := _), Prod.mk_add_mk, add_zero]
      map_smul' := second_factor_incl_smul R1 R2 }

theorem continuous_QQ_symm : Continuous (QQ (F := F) (E := E) R1 R2).symm := by
  exact (((continuous_first_factor_incl R1 R2).comp continuous_fst).add
    ((continuous_second_factor_incl R1 R2).comp continuous_snd)).congr
    fun p => (QQ_symm_eq_add R1 R2 p).symm

end Top

end Tens

end MassDataMassesW.SplitW
