module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open AddSubgroup

section Module

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

instance neZero_pow_prime (k : ℕ) : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.out.ne_zero⟩

end Module

end GroundTheory.Arith.Abelian
