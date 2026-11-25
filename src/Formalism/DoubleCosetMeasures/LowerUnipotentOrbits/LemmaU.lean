module

public import Formalism.DoubleCosetMeasures.StatementZ
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open MeasureTheory Matrix ComplexConjugate

namespace Formalism.DoubleCosetMeasures.P.LemmaU

open Formalism.DoubleCosetMeasures

section
variable {F : Type} [Field F] {a t : ℕ}

theorem choose_eq {J' : Subgroup (GL (Fin a) F)} {y : Matrix (Fin a) (Fin a) F}
    (h : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) (k : J')
    (e : ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) : Classical.choose h = k := by
  have hs := Classical.choose_spec h
  apply Subtype.ext
  apply Units.ext
  exact hs.trans e.symm

theorem toRows₁_mul (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₁ (x * g) = toRows₁ x * g := by
  ext i j
  simp [toRows₁, Matrix.mul_apply]

theorem toRows₂_mul (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₂ (x * g) = toRows₂ x * g := by
  ext i j
  simp [toRows₂, Matrix.mul_apply]

private theorem phiU_eq_zero_of_not_mem_support {O : Subring F} {ϖ : F} {J' : Subgroup (GL (Fin a) F)}
    {ρ : J' →* ℂˣ} {x : Matrix (Fin a ⊕ Fin t) (Fin a) F}
    (h : ¬ ((∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
      toRows₂ x ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)) :
    Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x = 0 := by
  simp only [Formalism.DoubleCosetMeasures.phiU]
  rw [dite_eq_right h]

theorem II_mul (O : Subring F) (ϖ : F) (y : Matrix (Fin t) (Fin a) F) (hy : y ∈ IIset O ϖ)
    (g : Matrix (Fin a) (Fin a) F) (hg : ∀ i j, g i j ∈ O) : y * g ∈ IIset O ϖ := by
  simp only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq] at hy ⊢
  choose o ho hyo using hy
  intro i j
  refine ⟨∑ k, o i k * g k j, O.sum_mem fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hyo i k, mul_assoc]

end

theorem suppJ' : SuppJ := by
  intro F _ _ a t O ϖ J' ρ χ nrm ν g hg
  unfold Formalism.DoubleCosetMeasures.weilIP
  have hz : ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
      Formalism.DoubleCosetMeasures.omegaS χ nrm g (Formalism.DoubleCosetMeasures.phiU (t := t) O ϖ J' ρ) x * conj (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x) = 0 := by
    intro x
    by_cases hx : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x
    · obtain ⟨k, hk⟩ := hx
      have h0 : Formalism.DoubleCosetMeasures.phiU (t := t) O ϖ J' ρ (x * (g : Matrix (Fin a) (Fin a) F)) = 0 := by
        apply phiU_eq_zero_of_not_mem_support
        rintro ⟨⟨k', hk'⟩, -⟩
        apply hg
        have e : ((k : GL (Fin a) F) * g : GL (Fin a) F) = k' := by
          apply Units.ext
          rw [Units.val_mul, hk, hk', toRows₁_mul]
        have hgk : g = (k : GL (Fin a) F)⁻¹ * k' := by
          rw [← e, inv_mul_cancel_left]
        rw [hgk]
        exact J'.mul_mem (J'.inv_mem k.2) k'.2
      simp only [Formalism.DoubleCosetMeasures.omegaS, h0, mul_zero, zero_mul]
    · rw [phiU_eq_zero_of_not_mem_support (fun h => hx h.1)]
      simp
  simp only [hz, integral_zero]

end Formalism.DoubleCosetMeasures.P.LemmaU

namespace Formalism.DoubleCosetMeasures.P

alias suppJ := _root_.Formalism.DoubleCosetMeasures.P.LemmaU.suppJ'

end Formalism.DoubleCosetMeasures.P
