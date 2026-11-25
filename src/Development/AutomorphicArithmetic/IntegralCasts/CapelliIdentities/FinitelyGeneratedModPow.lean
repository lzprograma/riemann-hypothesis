module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Finiteness.Ideal

@[expose] public section

namespace UpperTheory.Reformulated.B.FinitelyGeneratedModPow

/-- Finite generation modulo powers only requires the ideal to be finitely generated. -/
theorem fg_mod_pow_of_fg {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (m : Ideal A) (hm : m.FG) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n := by
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := Ideal.FG.pow hm
    have key : ∀ z ∈ Ideal.span (s : Set A),
        ∃ w ∈ Submodule.span O (s : Set A), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact ⟨z, Submodule.subset_span hz, by simp⟩
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, hw₁, e₁⟩ := h₁
        obtain ⟨w₂, hw₂, e₂⟩ := h₂
        refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
        have : z₁ + z₂ - (w₁ + w₂) = (z₁ - w₁) + (z₂ - w₂) := by ring
        rw [this]
        exact Ideal.add_mem _ e₁ e₂
      | smul a z hz h =>
        obtain ⟨w, hw, e⟩ := h
        obtain ⟨c, hc⟩ := hres a
        have hz' : z ∈ m ^ n := by rw [← hs]; exact hz
        refine ⟨c • w, Submodule.smul_mem _ c hw, ?_⟩
        have : a • z - c • w = z * (a - algebraMap O A c) + algebraMap O A c * (z - w) := by
          rw [smul_eq_mul, Algebra.smul_def]; ring
        rw [this]
        refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' hc
    refine ⟨N ⊔ Submodule.span O (s : Set A), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, e⟩ := key _ hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rwa [← sub_sub]

theorem fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n :=
  fg_mod_pow_of_fg m (IsNoetherian.noetherian m) hres n

end UpperTheory.Reformulated.B.FinitelyGeneratedModPow
