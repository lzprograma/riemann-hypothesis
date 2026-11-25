module

public import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Compare

section Nabla

variable {K : Type} [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}


omit [NumberField K] in
theorem pairK_basis [StarRing K] (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (i j : VVIdx lam) :
    pairK lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j) =
      pairBK lam (bVV K lam i) (rhoK lam g (bVV K lam j)) := by
  rw [pairK_apply, pairP_eq_pairB, pairBK_apply, rhoK_coe]
  congr 2
  rw [bVV_coe]
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [hQ, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

def gramB (K : Type) [Field K] (lam : ι → DomWeight n) : Matrix (VVIdx lam) (VVIdx lam) K :=
  Matrix.of fun i j => pairBK lam (bVV K lam i) (bVV K lam j)

omit [NumberField K] in
theorem gramB_transpose (lam : ι → DomWeight n) : (gramB K lam)ᵀ = gramB K lam := by
  ext i j
  simp only [gramB, Matrix.transpose_apply, Matrix.of_apply, pairBK_apply]
  exact pairingBSymm_holds K ι n lam _ _

end Nabla

end GlobalTheory.TestLat.Compare
