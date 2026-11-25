module

import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSplitSeqLinkInOrthogonalEqLinkIn
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

@[expose] public section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem mem_splitSeq_iff_pairwise (R : Type) [CommRing R] (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))) :
    l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧
      l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0 := by
  apply _root_.GlobalTheory.SeqCx.RowLink.mem_splitSeq_iff <;> assumption

theorem splitSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (splitSeq R n) := by
  intro l hl l' hs
  rw [mem_splitSeq_iff_pairwise] at hl ⊢
  exact ⟨fun y hy => hl.1 y (hs.subset hy), hl.2.sublist hs⟩

theorem mem_uniSeq_iff_exists_split (R : Type) [CommRing R] (n : ℕ) (w : List (Fin n → R)) :
    w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨List.ofFn fun i => (w.get i, f i), ?_, ?_⟩
    · intro i j
      have hi : (i : ℕ) < w.length := by simpa using i.2
      have hj : (j : ℕ) < w.length := by simpa using j.2
      have := hf ⟨i, hi⟩ ⟨j, hj⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn] at this ⊢
      simpa [Fin.ext_iff] using this
    · simp [List.map_ofFn]
      exact List.ofFn_get w
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => (l.get ⟨i, by simpa using i.2⟩).2, fun i j => ?_⟩
    have := hl ⟨i, by simpa using i.2⟩ ⟨j, by simpa using j.2⟩
    simp only [List.get_eq_getElem, List.getElem_map] at this ⊢
    simpa [Fin.ext_iff] using this

theorem uniSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (uniSeq R n) := by
  intro w hw w' hs
  rw [mem_uniSeq_iff_exists_split] at hw ⊢
  obtain ⟨l, hl, rfl⟩ := hw
  obtain ⟨l', hl', rfl⟩ := List.sublist_map_iff.mp hs
  exact ⟨l', splitSeq_sublist_closed R n l hl l' hl', rfl⟩

end GlobalTheory.SeqCx

theorem GlobalTheory.SeqCx.split_uni_closed : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) :=
  fun R _ n => ⟨splitSeq_sublist_closed R n, uniSeq_sublist_closed R n, mem_splitSeq_iff_pairwise R n, mem_uniSeq_iff_exists_split R n⟩

