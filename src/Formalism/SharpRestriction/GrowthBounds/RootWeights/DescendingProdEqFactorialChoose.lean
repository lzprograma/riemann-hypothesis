module

import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolarizationDividedPowerSumSucc
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpCon

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ}

def polarizationSource (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, b) else (l, a)

def polarizationTarget (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, a) else (l, b)

def polarizationLetterSign (R : Type*) [CommRing R] (LL : Letters ι) (l : ι) : R := if LL.vec l then 1 else -1

theorem glAct_pow_eq_factorial_divPow (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    (glAct R LL S a b : Module.End R (MvPolynomial (ι × Fin n) R)) ^ k = k.factorial • divPow R LL S a b k := by
  apply _root_.Formalism.MainNotions.LemmaBAlt.gl_action_pow_eq_factorial_smul <;> assumption

theorem X_mul_pderiv_monomial' {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    X v * pderiv v (monomial m c) = ((m v : ℕ) : R) • monomial m c := by
  classical
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]

theorem glAct_diagonal_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = ((wtS LL S m a : ℤ) : R) • monomial m c := by
  classical
  rw [glAct, LinearMap.sum_apply, wtS, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp_all [-MvPolynomial.pderiv_monomial, X_mul_pderiv_monomial']

theorem list_prod_shifted_eigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (w : K) (x : V)
    (h : T x = w • x) (L : List ℕ) :
    ((L.map fun j : ℕ => T - (j : K) • (1 : Module.End K V)).prod) x = ((L.map fun j : ℕ => w - (j : K)).prod) • x := by
  induction L with
  | nil => simp
  | cons j L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h]
    rw [← sub_smul, smul_smul, mul_comm]

theorem list_range_prod_eq_finset_prod {K : Type*} [CommRing K] (w : K) (k : ℕ) :
    ((List.range k).map fun j : ℕ => w - (j : K)).prod = ∏ j ∈ Finset.range k, (w - (j : K)) := by
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.prod_coe]

theorem descending_prod_eq_factorial_choose (z : ℤ) (k : ℕ) : ∏ j ∈ Finset.range k, (z - (j : ℤ)) = (k.factorial : ℤ) * Ring.choose z k := by
  rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

end v2dpCon

theorem dividedPower_formula_char_zero : DividedPowerFormulaCharZero := by
  intro R _ _ ι _ LL n S a b k hab
  show ((k.factorial : R)⁻¹) • (glAct R LL S a b) ^ k = divPow R LL S a b k
  rw [glAct_pow_eq_factorial_divPow LL S a b hab k, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

theorem binomial_formula_char_zero : BinomialFormulaCharZero := by
  intro R _ _ ι _ LL n S a k
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials]
  show ((k.factorial : R)⁻¹ • ((List.range k).map fun j : ℕ =>
    glAct R LL S a a - (j : R) • (1 : Module.End R (MvPolynomial (ι × Fin n) R))).prod) (monomial m 1) = _
  rw [LinearMap.smul_apply, list_prod_shifted_eigen (glAct R LL S a a) ((wtS LL S m a : ℤ) : R) (monomial m 1)
    (glAct_diagonal_monomial LL S a m 1), list_range_prod_eq_finset_prod, smul_smul]
  have hc : ∏ j ∈ Finset.range k, (((wtS LL S m a : ℤ) : R) - (j : R)) =
      (((k.factorial : ℤ) * Ring.choose (wtS LL S m a) k : ℤ) : R) := by
    rw [← descending_prod_eq_factorial_choose]
    push_cast
    rfl
  rw [hc]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

end Formalism.MainNotions.G.GLWeightTheory
