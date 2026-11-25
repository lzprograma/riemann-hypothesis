module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToAdditive

@[expose] public section

namespace GlobalTheory.DiagVol

def ordL {n : Type*} (c : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => c + 1) (fun i => 2 * (i.val + 1))

end GlobalTheory.DiagVol
