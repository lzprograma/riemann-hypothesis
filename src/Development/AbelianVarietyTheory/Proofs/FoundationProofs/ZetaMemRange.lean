module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

open Polynomial

namespace GlobalTheory.KummerCob

theorem zeta_mem_range : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Field Ω] [Algebra K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → ζ ∈ Set.range (algebraMap K Ω) := by
  intro k K Ω _ _ _ _ _ _ _ N ζ hN hζ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : k) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  let φ : k →+* Ω := (algebraMap K Ω).comp ((algebraMap k[X] K).comp Polynomial.C)
  have hφ : Function.Injective φ := φ.injective
  have hξ' : IsPrimitiveRoot (φ ξ) N := hξ.map_of_injective hφ
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine ⟨(algebraMap k[X] K (Polynomial.C ξ)) ^ i, ?_⟩
  rw [map_pow, ← hi]
  rfl

end GlobalTheory.KummerCob
