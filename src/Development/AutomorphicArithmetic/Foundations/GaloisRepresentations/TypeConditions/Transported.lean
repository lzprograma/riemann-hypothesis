module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N

namespace UpperTheory.GalS


open Classical in
def thr {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : ℕ :=
  if ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (n = 1 ∨ 16 * n ^ 2 < p) then 2 else 1

theorem thr_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} : 0 < thr w n := by
  unfold thr
  split_ifs <;> norm_num

theorem thr_split {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {p : ℕ} (hp : p.Prime)
    (hw : w ∈ placesOver E p) (hs : (placesOver E p).ncard = Module.finrank ℚ E) {n : ℕ} (hn : 16 * n ^ 2 < p) :
    thr w n = 2 := ite_eq_left ⟨p, hp, hw, hs, Or.inr hn⟩

theorem thr_anti {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {m n : ℕ} (h : m ≤ n) : thr w n ≤ thr w m := by
  unfold thr
  by_cases hm : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (m = 1 ∨ 16 * m ^ 2 < p)
  · rw [ite_eq_left hm]
    split_ifs <;> norm_num
  · rw [ite_eq_right hm]
    have hn : ¬ ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (n = 1 ∨ 16 * n ^ 2 < p) := by
      rintro ⟨p, hp, hw, hs, hc⟩
      apply hm
      refine ⟨p, hp, hw, hs, ?_⟩
      rcases hc with rfl | hc
      · interval_cases m
        · right
          simpa using hp.pos
        · left
          rfl
      · right
        have : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
        omega
    rw [ite_eq_right hn]

end UpperTheory.GalS
