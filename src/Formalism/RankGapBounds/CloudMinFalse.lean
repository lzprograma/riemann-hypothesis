module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace Formalism.RankGapBounds.JumpSetsAlt

open Finset

def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l

def posPairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

def eExp {N : ℕ} (U : Fin N → ℤ) (l : ℕ) : ℕ :=
  ∑ p ∈ posPairs N, maxVal l (U p.1 - U p.2 - 1).toNat

end Formalism.RankGapBounds.JumpSetsAlt
