module

import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Lemmata.GeneralBFactLeftSide.Imports

@[expose] public section

open MvPolynomial Matrix Formalism.GradedWeylDivisibility

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

alias prodSpan := _root_.Bl.general_b_fact_left'''''.goal1

theorem rowAct_one {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) F = F := by
  have e : rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [rowAct, aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e]; rfl

theorem rowAct_cancel {R : Type} [CommRing R] {r n : ℕ} (g gi : Matrix (Fin r) (Fin r) R) (h : gi * g = 1)
    (F : MvPolynomial (Fin r × Fin n) R) : rowAct R g (rowAct R gi F) = F := by
  have h1 := rowActMul R r n g gi
  rw [h] at h1
  have h2 := congrArg (fun f => f F) h1
  simp only [AlgHom.comp_apply] at h2
  rw [h2, rowAct_one]

theorem map_mem_weyl {O : Type} [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    MvPolynomial.map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  apply _root_.Formalism.L2.Col.map_mem_weyl <;> assumption

theorem weyl_eq_span_int (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    weyl O r n hn ν = Submodule.span O ((fun f => MvPolynomial.map (Int.castRingHom O) f) ''
      (weyl ℤ r n hn ν : Set (MvPolynomial (Fin r × Fin n) ℤ))) := by
  apply le_antisymm
  · show Submodule.span O (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord O w (hw O hn ν)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    exact ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, by
      show MvPolynomial.map (Int.castRingHom O) (applyWord ℤ w (hw ℤ hn ν)) = _
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact map_mem_weyl hn ν f hf

end Formalism.L2.G.RelativeIndexFlags.Core
