module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

namespace GroundTheory.Heights₂.Heights.RestTerms

open Polynomial Finset

theorem SchProdOneSubRootsOfUnity.proof : SchProdOneSubRootsOfUnity.Statement := by
  intro k hk
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hζ : IsPrimitiveRoot (rootOfUnity k) k := Complex.isPrimitiveRoot_exp k (NeZero.ne k)
  refine eq_of_degree_sub_lt_of_eval_finset_eq (insert 0 (nthRootsFinset k 1)) ?_ fun x hx => ?_
  · rw [card_insert_of_notMem (by simp [mem_nthRootsFinset hk, zero_pow (NeZero.ne k)]),
      hζ.card_nthRootsFinset]
    refine (degree_le_of_natDegree_le (n := k) ?_).trans_lt (by exact_mod_cast Nat.lt_succ_self k)
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by compute_degree))
    refine (natDegree_prod_le _ _).trans ?_
    exact (sum_le_sum (g := fun _ => 1) (fun i _ => by compute_degree)).trans (by simp)
  · rcases mem_insert.mp hx with rfl | hx
    · simp [eval_prod, zero_pow (NeZero.ne k)]
    · have hxk := (mem_nthRootsFinset hk _).mp hx
      obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one (show x⁻¹ ^ k = 1 by simp [inv_pow, hxk])
      simp only [eval_prod, eval_sub, eval_one, eval_pow, eval_X, hxk, sub_self]
      apply prod_eq_zero (mem_range.mpr hi)
      simp [hi', inv_mul_cancel₀ (ne_zero_of_mem_nthRootsFinset one_ne_zero hx)]

end GroundTheory.Heights₂.Heights.RestTerms
