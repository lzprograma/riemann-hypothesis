module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Ring.Associated
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

noncomputable section

namespace RootsOfUnityValuation

variable {A : Type*} [CommRing A] [IsDomain A]


omit [IsDomain A] in
theorem associated_sub_comm (a b : A) : Associated (a - b) (b - a) :=
  ⟨-1, by simp⟩

theorem one_sub_pow_associated {l : ℕ} (hl : l.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ l) :
    Associated ((1 - ζ) ^ (l - 1)) (l : A) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
  have h := hζ.prod_one_sub_pow_eq_order
  have h1 : (1 - ζ) ^ n = ∏ _k ∈ range n, (1 - ζ) := by simp
  rw [Nat.succ_sub_one, h1]
  push_cast
  rw [← h]
  refine Associated.prod _ _ _ fun k hk => ?_
  have hcop : (k + 1).Coprime (n + 1) :=
    (Nat.coprime_of_lt_prime (by lia) (by simpa using Finset.mem_range.1 hk) hl).symm
  simpa only [neg_sub] using (hζ.associated_sub_one_pow_sub_one_of_coprime hcop).neg_neg

end RootsOfUnityValuation

end

end GroundTheory.Heights₂.Heights
