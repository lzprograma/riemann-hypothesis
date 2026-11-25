module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

noncomputable section

open CategoryTheory UpperTheory.V.KL

namespace UpperTheory.V.Published

/-- If `R` has stable rank at most `s` and `n ≥ 2 * i + s + 2`, then `A ↦ diag(A, 1)` induces an
isomorphism `H_i(GL_n(R); ℤ) → H_i(GL_{n+1}(R); ℤ)`. -/
def KStability : Prop :=
  ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i n : ℕ, 2 * i + s + 2 ≤ n →
    IsIso (grpHMap (stab R n (n + 1) (Nat.le_succ n)) i)

end UpperTheory.V.Published

end
