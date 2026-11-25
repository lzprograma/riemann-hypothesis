module

public import Formalism.PadicSubsetSums.CentralIdempotents.SchurOrthogonalityCompact
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

open scoped NumberField

namespace Formalism.IrreducibleCountingLemmas.Z

theorem degree_one_split : DegreeOneSplit := by
  intro F E _ _ _ _ _ h2 P _ hP hf he
  classical
  let p := P.under (𝓞 F)
  let _ : Fintype (p.primesOver (𝓞 E)) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  let Q : p.primesOver (𝓞 E) := ⟨P, inferInstance, ⟨rfl⟩⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ Q), he, one_mul,
    Nat.eq_one_of_mul_eq_one_left ((Ideal.inertiaDeg_tower (R := ℤ) p P).symm.trans hf),
    Nat.one_add, Nat.succ.injEq] at hsum
  rw [← Set.fintypeCard_eq_ncard, ← Finset.card_univ,
    ← Finset.card_erase_add_one (Finset.mem_univ Q)]
  obtain h | h := (Finset.univ.erase Q).eq_empty_or_nonempty
  · simp [h] at hsum
  · refine congrArg (· + 1) (Nat.le_antisymm ?_ h.card_pos)
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun q _ =>
      Nat.mul_pos (Ideal.ramificationIdx_pos (R := 𝓞 F) q.1) (Ideal.inertiaDeg_pos q.1 (𝓞 F))

end Formalism.IrreducibleCountingLemmas.Z
