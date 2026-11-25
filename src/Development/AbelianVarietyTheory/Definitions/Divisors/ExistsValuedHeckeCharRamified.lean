module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.Model

section General

variable {E : Type} [Field E] [NumberField E]

theorem IsCMType.bijective {I : Type} {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

end General

end GlobalTheory.CMVal.Model
