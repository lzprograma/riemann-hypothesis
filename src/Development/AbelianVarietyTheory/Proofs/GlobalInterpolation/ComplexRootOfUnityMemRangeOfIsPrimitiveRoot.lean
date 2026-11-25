module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

namespace GlobalTheory

theorem complex_rootOfUnity_mem_range_of_isPrimitiveRoot :
    ∀ (K : Type) [Field K] (s : K →+* ℂ) (n : ℕ) (ζ : K), 0 < n → IsPrimitiveRoot ζ n →
      ∀ z : ℂ, z ^ n = 1 → ∃ r : K, s r = z := by
  intro K _ s n ζ hn hζ z hz
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : IsPrimitiveRoot (s ζ) n := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

end GlobalTheory
