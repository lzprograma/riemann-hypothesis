module

public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Group.Submonoid.Membership

@[expose] public section

/-- If a set is closed under scalar multiplication, every element of its span is a finite
sum of elements of the set. -/
theorem Submodule.exists_list_of_mem_span {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {s : Set M} (hs : ∀ {v}, v ∈ s → ∀ c : R, c • v ∈ s) {y : M} (hy : y ∈ span R s) :
    ∃ l : List M, (∀ w ∈ l, w ∈ s) ∧ y = l.sum := by
  change y ∈ (span R s).toAddSubmonoid at hy
  rw [Submodule.span_eq_closure] at hy
  obtain ⟨l, hl, hsum⟩ := AddSubmonoid.exists_list_of_mem_closure hy
  refine ⟨l, fun w hw => ?_, hsum.symm⟩
  obtain ⟨c, _, v, hv, rfl⟩ := hl w hw
  exact hs hv c
