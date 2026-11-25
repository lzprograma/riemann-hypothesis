module

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BRawHeadColsRight
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DetSmulMk
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgInj
import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem bRaw_e (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y : Fin (r + 1) → O) :
    bRaw O cj Z y (Pi.single (Fin.last r) 1) = lamL O Z y := by
  unfold bRaw
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp [lamL, lamC]
  · intro j _ hj
    simp [hj]
  · simp

theorem bRaw_b_mem (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y : Fin (r + 1) → O) : bRaw O cj Z y (fun i => cjT O cj hO Z i (Fin.last r)) ∈ O := by
  unfold bRaw
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : ∀ j, cj ((cjT O cj hO Z j (Fin.last r) : O) : E) = (Z.map O.subtype) (Fin.last r) j := fun j => hcj _
  simp only [e]
  rw [show ∑ j, (Z.map O.subtype) (Fin.last r) j * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j =
      ((Z.map O.subtype).mulVec ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E)))) (Fin.last r) from rfl,
    Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact (y _).2

theorem lamS_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) (w : Fin (r + 1) → O) :
    lamS O cj Z ((cjT O cj hO Z).mulVec w) = (w (Fin.last r) : E) := by
  unfold lamS lamStarC
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hcoe : ∀ b, (((cjT O cj hO Z).mulVec w b : O) : E) = ∑ c, cj ((Z c b : O) : E) * (w c : E) := by
    intro b
    simp [Matrix.mulVec, dotProduct, cjT]
  simp only [hcoe, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow : ∀ c, ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * (cj ((Z c b : O) : E) * (w c : E)) =
      cj (if c = Fin.last r then 1 else 0) * (w c : E) := by
    intro c
    have h1 := congrFun (congrFun hinv c) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1

    rw [← h1, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul]
    simp only [Matrix.map_apply, Subring.coe_subtype]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hrow c)]
  simp [apply_ite cj]

theorem lamS_K (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) (k : Fin (r + 1) → O)
    (hk : k ∈ headCols (cjT O cj hO Z)) : lamS O cj Z k = 0 := by
  apply _root_.Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear.lamS_headCols <;> assumption

theorem lamS_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) :
    lamS O cj Z (fun i => cjT O cj hO Z i (Fin.last r)) = 1 := by
  unfold lamS lamStarC
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h1 := congrFun (congrFun hinv (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have key : ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * ((cjT O cj hO Z b (Fin.last r) : O) : E) =
      cj (∑ b, (Z.map O.subtype) (Fin.last r) b * (Z.map O.subtype)⁻¹ b (Fin.last r)) := by

    rw [map_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul, mul_comm]
    rfl
  rw [key, h1, map_one]

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

theorem pair_b (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (p : PairSet O cj hO Z₁ Z₂) : p.1.2 (bCls (cjT O cj hO Z₁)) = bCls (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (bCls (cjT O cj hO Z₁)))
  rw [← hy, bCls, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply mk_eq_zero_of O cj hcj hO Z₂ hu₂
  · intro y
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (p.1.1.symm (Submodule.Quotient.mk y))
    have e1 : p.1.1 (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y := by
      rw [hy₁]; exact p.1.1.apply_symm_apply _
    have A := p.2.2.2 y₁ _ y y₂' e1 hy.symm
    rw [bRaw_sub_right]
    have B := O.add_mem A (bRaw_b_mem O cj hcj hO Z₁ hu₁ y₁)
    rw [sub_add_cancel] at B
    exact O.sub_mem B (bRaw_b_mem O cj hcj hO Z₂ hu₂ y)
  · rw [lamS_sub, p.2.2.1 _ y₂' hy.symm, lamS_b O cj Z₁ hO hu₁, lamS_b O cj Z₂ hO hu₂, sub_self]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
