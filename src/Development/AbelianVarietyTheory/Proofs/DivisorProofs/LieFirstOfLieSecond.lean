module

import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MvPolynomial Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.LieFirstPf

variable {P Q R S : ℕ}

def swapE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

theorem swapE_apply (f : Formalism.BasicNotions.TH.Pol R S P Q) : swapE P Q R S f = rename Prod.swap f := rfl

theorem lineSign_swap (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem swapE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    swapE P Q R S (heisOp c f) = heisOp cᵀ (swapE P Q R S f) := by

  simp only [heisOp, swapE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
  map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_swap]

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def swapT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => swapE P Q R S

theorem swapT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, swapE P Q R S (L' f) = L (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (atPl w L' T) = atPl w L (swapT ι P Q R S T) := by
  have e : (swapT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, swapE P Q R S (L' w f) = L w (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (sumPl L' T) = sumPl L (swapT ι P Q R S T) := by

  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapT_atPl w (L' w) (L w) (h w) T

end Tensor


open scoped Classical in
theorem lieFirst_of_lieSecond : LieSecond → LieFirst := by
  apply PositivityTheory.RL.lieFirst

end GlobalTheory.RealLift.LieFirstPf
