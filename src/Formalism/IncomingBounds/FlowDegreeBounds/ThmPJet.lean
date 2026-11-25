module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame
public import Formalism.IncomingBounds.StatementThmP

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

section
variable {C : Type} [Field C]

theorem tpjet_jetAt0_superset {σ : Type} (P : MvPolynomial σ C) (G : MvPowerSeries σ C)
    (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jetAt0 P G = ∑ m ∈ S, AddMonoidAlgebra.coeff P m * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]

theorem tpjet_jetAt0_add {σ : Type} (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  apply GlobalTheory.MinorShiftJet.jetAt0_add_left

theorem tpjet_jetAt0_zero {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  unfold jetAt0
  simp

theorem tpjet_jetAt0_sum {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, tpjet_jetAt0_zero]
  · intro j t hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

end
end Formalism.IncomingBounds
