module

public import Formalism.SatakeDualWeyl.Statement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg

@[expose] public section

noncomputable section

namespace PIW.AdelicOrbitU

open Matrix Formalism.UG

section Refl

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem hform_eq_dot (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_left (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by
  simp only [hform_eq_dot, dotProduct, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y z : Fin n → S) :
    hform s J x (y - z) = hform s J x y - hform s J x z := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_left (a : S) (x y : Fin n → S) :
    hform s J (a • x) y = s a * hform s J x y := by
  simp only [hform_eq_dot, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem hform_conj (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by
  apply _root_.Formalism.L2.SG.Pf.NcS.IntWittAlg.hform_conj <;> assumption

end Refl

end PIW.AdelicOrbitU
