module

import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalNeZeroOfMemCellMon
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreLast
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerBis
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraBis
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreMore

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem cellSec_mono [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) {I I' : ∀ k, Finset (ι k)} (h : ∀ k, I k ⊆ I' k)
    (hI' : CellMeets y I') : cellSec S y γ I ≤ cellSec S y γ I' := by
  apply RowLocCover.cellSec_mono <;> assumption

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem baseCell_mono (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {J J' : Finset (Fin (N + 1))}
    {I I' : ∀ k, Finset (ι k)} (hJ : J ⊆ J') (hI : ∀ k, I k ⊆ I' k) (k : K) :
    baseCell k₀ e J I k ⊆ baseCell k₀ e J' I' k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self, Function.update_self]
    exact Finset.union_subset_union (hI k) (Finset.map_subset_map.mpr hJ)
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]; exact hI k

theorem ModelCechRefine.proof (hC : CechContract.Statement) (hR : ModelRowExact.Statement)
    (hD : DoubleCech.Statement) : ModelCechRefine.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ T hT n
  have hM0 : ∀ (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, ¬ CellMeets y I →
      cellSec F y γ (baseCell k₀ e J.1 I) = ⊥ := fun J I hI => by
    unfold cellSec
    rw [ite_eq_right fun h => hI fun k i hi => h k i (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowLocCover.subset_baseCell k₀ e J.1 I k hi)]
  have hMJ : ∀ (J J' : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, J.1 ⊆ J'.1 →
      cellSec F y γ (baseCell k₀ e J.1 I) ≤ cellSec F y γ (baseCell k₀ e J'.1 I) := fun J J' I h => by
    by_cases hI : CellMeets y I
    · exact cellSec_mono y γ (baseCell_mono k₀ e h fun _ => subset_rfl) (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowLocCover.cellMeets_baseCell y k₀ e J' hI)
    · rw [hM0 J I hI]; exact bot_le
  refine (hD F K ι Ω y N _ T (cellSec F y γ) (fun J I => cellSec F y γ (baseCell k₀ e J.1 I)) hM.1 ?_
    (fun I hI => by unfold cellSec; rw [ite_eq_right hI]) hM0 hMJ
    (fun J I I' h hI' => cellSec_mono y γ (baseCell_mono k₀ e subset_rfl h) (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowLocCover.cellMeets_baseCell y k₀ e J hI'))
    ?_ ?_ n)
  · obtain ⟨i, hi⟩ := hM.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  · intro I hne hI
    obtain ⟨i, hi⟩ := hne k₀
    have hx : (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (e i) ≠ 0 := by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hI k₀ i hi
    let J₀ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) :=
      ⟨{e i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr ((Kleiman.mem_support _).mpr hx)⟩
    have hadd : ∀ J : Finset (Fin (N + 1)), baseCell k₀ e ({e i} ∪ J) I = baseCell k₀ e J I := by
      intro J
      unfold baseCell
      congr 1
      rw [Finset.map_union, ← Finset.union_assoc, Finset.map_singleton]
      congr 1
      exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (by simpa using hi))
    have h₀ : baseCell k₀ e J₀.1 I = I := by
      have := hadd ∅
      rw [Finset.union_empty] at this
      rw [show J₀.1 = {e i} from rfl, this]
      unfold baseCell
      simp
    have := hC F Ω N _ (fun J => cellSec F y γ (baseCell k₀ e J.1 I)) J₀ (Finset.card_singleton _)
      (fun J J' h => hMJ J J' I h) (fun J J' h => by
        show cellSec F y γ (baseCell k₀ e J'.1 I) = _
        rw [h]; exact congrArg _ (hadd J.1))
    simpa only [h₀] using this
  · intro J
    have h := hR F K ι Ω y k₀ N e hM γ J
    rwa [← hT J, ← Submodule.coe_restrictScalars F, Submodule.span_eq] at h

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
