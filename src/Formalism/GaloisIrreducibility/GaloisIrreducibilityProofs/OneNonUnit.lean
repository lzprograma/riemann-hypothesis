module

public import Mathlib.Data.Nat.Notation
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.Lemma
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.RingTheory.LocalRing.Defs

@[expose] public section

namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

end BorderedIndexCases



end Formalism.GaloisIrreducibility
