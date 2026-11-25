module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.AlmostEverywhereSpherical
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TMemLaurentFiltration
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Bool


-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.SumCCMulSumOfMulEqOne =====
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

abbrev flt_tay (R : Type*) [CommRing R] (σ : Type*) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_tay R σ

abbrev flt_g (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_g R m be

alias flt_g_pascal := Formalism.MainNotions.G.GLWeightTheory.flt_g_pascal
alias flt_tay_monomial := Formalism.MainNotions.G.GLWeightTheory.flt_tay_monomial
alias flt_tay_coeff := Formalism.MainNotions.G.GLWeightTheory.flt_tay_coeff

abbrev flt_Th {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_Th (R := R) LL S j
alias sum_C_C_mul_sum_of_mul_eq_one := Formalism.MainNotions.G.GLWeightTheory.sum_C_C_mul_sum_of_mul_eq_one
alias flt_Th_twist := Formalism.MainNotions.G.GLWeightTheory.flt_Th_twist
alias flt_Th_mem := Formalism.MainNotions.G.GLWeightTheory.flt_Th_mem
alias flt_divDer_mem := Formalism.MainNotions.G.GLWeightTheory.flt_divDer_mem
alias flt_op_mem := Formalism.MainNotions.G.GLWeightTheory.flt_op_mem
theorem flt_op_mem_val {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {t : ℤ} (ht : (t : WithTop ℤ) ≤ valS LL S F) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    twistSub LL S (lastIdx n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F (t - N) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_op_mem_val LL S ht al be N hN

theorem flt_op_mem_lam {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {M : ℤ} (hM : lam1S LL S F ≤ (M : WithBot ℤ)) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    twistSub LL S (0 : Fin n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-(M + N)) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_op_mem_lam LL S hM al be N hN

theorem flt_op_valS {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + ((N : ℤ) : WithTop ℤ) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_op_valS LL S F al be N hN

theorem flt_op_lam1S {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    lam1S LL S (monomial al 1 * divDer be F) ≤ lam1S LL S F + ((N : ℤ) : WithBot ℤ) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_op_lam1S LL S F al be N hN

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.SumCCMulSumOfMulEqOne =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne =====
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

theorem coeff_divDer (be μ : ι × Fin n →₀ ℕ) (F : MvPolynomial (ι × Fin n) R) :
    AddMonoidAlgebra.coeff (divDer be F) μ = AddMonoidAlgebra.coeff F (μ + be) * ((be.prod fun k j => ((μ + be) k).choose j : ℕ) : R) := by
  classical
  rw [divDer, coeff_sum]
  rw [Finset.sum_congr rfl (g := fun m => if m = μ + be then
      AddMonoidAlgebra.coeff F m * ((be.prod fun k j => (m k).choose j : ℕ) : R) else 0)]
  · rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, zero_mul]
  · intro m _
    by_cases h1 : be ≤ m
    · rw [ite_eq_left h1, coeff_monomial]
      by_cases h2 : m = μ + be
      · subst h2
        rw [ite_eq_left (add_tsub_cancel_right μ be), ite_eq_left rfl]
      · rw [ite_eq_right h2, ite_eq_right]
        intro h3
        apply h2
        rw [← h3, tsub_add_cancel_of_le h1]
    · rw [ite_eq_right h1, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_eq_right]
      rintro rfl
      exact h1 le_add_self

theorem divDer_zero' (F : MvPolynomial (ι × Fin n) R) : divDer 0 F = F := by
  ext μ
  rw [coeff_divDer]
  simp

theorem divDer_single_one (v : ι × Fin n) (F : MvPolynomial (ι × Fin n) R) :
    divDer (Finsupp.single v 1) F = pderiv v F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    ext μ
    rw [coeff_divDer, pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = μ + Finsupp.single v 1
    · subst h
      rw [ite_eq_left rfl, ite_eq_left (add_tsub_cancel_right μ _)]
      simp [Finsupp.prod_single_index, Nat.choose_one_right]
    · rw [ite_eq_right h, zero_mul]
      split_ifs with h2
      · have hv : u v = 0 := by
          by_contra hv
          have hle : Finsupp.single v 1 ≤ u :=
            Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          apply h
          rw [← h2, tsub_add_cancel_of_le hle]
        rw [hv, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq =>
    rw [map_add (f := _), ← hp, ← hq]
    ext μ
    rw [MvPolynomial.coeff_add, coeff_divDer, coeff_divDer, coeff_divDer, MvPolynomial.coeff_add, add_mul]

theorem vecDeg_zero' (S : Set ι) : vecDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [vecDeg, Formalism.MainNotions.CovariantDegrees.vecDeg]

theorem covDeg_zero' (S : Set ι) : covDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [covDeg, Formalism.MainNotions.CovariantDegrees.covDeg]

theorem vecDeg_single_le (S : Set ι) (v : ι × Fin n) : vecDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [vecDeg, Formalism.MainNotions.CovariantDegrees.vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

theorem covDeg_single_le (S : Set ι) (v : ι × Fin n) : covDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [covDeg, Formalism.MainNotions.CovariantDegrees.covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

theorem vecDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    vecDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [vecDeg, Formalism.MainNotions.CovariantDegrees.vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, ite_eq_right]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

theorem covDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    covDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [covDeg, Formalism.MainNotions.CovariantDegrees.covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, ite_eq_right]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

theorem X_eq_monomial' (v : ι × Fin n) : (X v : MvPolynomial (ι × Fin n) R) = monomial (Finsupp.single v 1) 1 := rfl

theorem twistSub_X_out (j : Fin n) (v : ι × Fin n) (h : v.1 ∉ S) :
    twistSub (R := R) LL S j (X v) = X v := by
  simp [twistSub, h]

theorem valS_X_mul_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    valS LL S F ≤ valS LL S (X v * F) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 0
    (by rw [covDeg_single_of LL S v h, vecDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithTop.coe_zero, add_zero] at hv
  exact hv

theorem valS_X_mul (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (X v * F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 1
    (by rw [vecDeg_zero', add_zero]; exact covDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

theorem valS_pderiv_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    valS LL S F ≤ valS LL S (pderiv v F) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 0
    (by rw [covDeg_zero', vecDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithTop.coe_zero, add_zero] at hv
  exact hv

theorem valS_pderiv (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (pderiv v F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 1
    (by rw [covDeg_zero', zero_add]; exact vecDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv

theorem maxTwistDegree_X_mul_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    lam1S LL S (X v * F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 0
    (by rw [vecDeg_single_of LL S v h, covDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithBot.coe_zero, add_zero] at hv
  exact hv

theorem maxTwistDegree_X_mul_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (X v * F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 1
    (by rw [covDeg_zero', add_zero]; exact vecDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

theorem maxTwistDegree_pderiv_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 0
    (by rw [vecDeg_zero', covDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithBot.coe_zero, add_zero] at hv
  exact hv

theorem maxTwistDegree_pderiv_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 1
    (by rw [vecDeg_zero', zero_add]; exact covDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne =====
