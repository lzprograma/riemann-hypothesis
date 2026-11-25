module

public import Formalism.TameInertiaTowers.StatementGroup
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace Formalism.TwoAdicCyclotomicDecomposition

namespace AdmissibleUnits

def r4 (N : ℕ) (h : 4 ∣ 2 ^ N) : (ZMod (2 ^ N))ˣ →* ZMod 4 :=
  (ZMod.castHom h (ZMod 4)).toMonoidHom.comp (Units.coeHom _)

lemma mod_four_reduction_five (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (u5 N) = 1 := by
  unfold u5
  show (ZMod.castHom h (ZMod 4)) ((5 : ℕ) : ZMod (2 ^ N)) = 1
  rw [map_natCast]
  decide

lemma mod_four_reduction_neg_one (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (-1) = -1 := by
  show (ZMod.castHom h (ZMod 4)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

private lemma exists_one_add_two_pow_odd_pow_two_pow_eq (i m0 : ℕ) : ∀ k : ℕ, ∃ m : ℕ,
    (1 + 2 ^ (i + 2) * (2 * m0 + 1)) ^ (2 ^ k) = 1 + 2 ^ (k + (i + 2)) * (2 * m + 1) := by
  intro k
  induction k with
  | zero => exact ⟨m0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 2 ^ (i + k) * (2 * m + 1) ^ 2, ?_⟩
    rw [pow_succ 2 k, pow_mul, hm]
    ring

private lemma natCast_one_add_two_pow_mul_eq_one (N q : ℕ) : ((1 + 2 ^ N * q : ℕ) : ZMod (2 ^ N)) = 1 := by
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, Nat.cast_one]

private lemma natCast_one_add_two_pow_odd_ne_one (N m : ℕ) :
    ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) ≠ 1 := by
  intro h
  have h' : ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) = ((1 : ℕ) : ZMod (2 ^ (N + 1))) := by
    rw [h, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have h2 := (Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).1 h'.symm
  rw [Nat.add_sub_cancel_left, pow_succ] at h2
  have h3 := Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos N) h2
  omega

private lemma unitOfCoprime_pow_eq_one_iff (N a e : ℕ) (h : Nat.Coprime a (2 ^ N)) :
    (ZMod.unitOfCoprime a h) ^ e = 1 ↔ ((a ^ e : ℕ) : ZMod (2 ^ N)) = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Nat.cast_pow]

lemma orderOf_five_units_two_pow (n : ℕ) : orderOf (u5 (n + 2)) = 2 ^ n := by
  unfold u5
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff]
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  | succ n =>
    apply orderOf_eq_prime_pow
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 n
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_odd_ne_one _ _
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 (n + 1)
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_mul_eq_one _ _

lemma sign_eq (n : ℕ) {b b' : Bool} {k k' : ℕ}
    (h : (if b then -1 else 1) * u5 (n + 3) ^ k = (if b' then -1 else 1) * u5 (n + 3) ^ k') :
    b = b' := by
  have h4 : 4 ∣ 2 ^ (n + 3) := ⟨2 ^ (n + 1), by ring⟩
  have hr : ∀ c : Bool, r4 (n + 3) h4 (if c then -1 else 1) = if c then -1 else 1 := by
    intro c
    cases c
    · exact map_one _
    · exact mod_four_reduction_neg_one _ _
  have := congrArg (r4 (n + 3) h4) h
  rw [map_mul, map_mul, hr, hr, map_pow, map_pow, mod_four_reduction_five, one_pow, one_pow, mul_one, mul_one] at this
  cases b <;> cases b'
  · rfl
  · exact absurd this (by decide)
  · exact absurd this (by decide)
  · rfl

lemma inj (n : ℕ) : Function.Injective (fun p : Bool × Fin (2 ^ (n + 1)) =>
    (if p.1 then -1 else 1) * u5 (n + 3) ^ (p.2 : ℕ)) := by
  rintro ⟨b, k⟩ ⟨b', k'⟩ h
  have hb : b = b' := sign_eq n h
  subst hb
  have h2 : u5 (n + 3) ^ (k : ℕ) = u5 (n + 3) ^ (k' : ℕ) := mul_left_cancel h
  have ho : orderOf (u5 (n + 3)) = 2 ^ (n + 1) := orderOf_five_units_two_pow (n + 1)
  rw [pow_inj_mod, ho, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h2
  exact Prod.ext rfl (Fin.ext h2)

end AdmissibleUnits

end Formalism.TwoAdicCyclotomicDecomposition
