module

import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCGradAtlas
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
import Mathlib.Tactic.Linter.Style

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  apply PositivityTheory.Xgp.c_grad_atlas.isOpen_compl_bdry <;> assumption

theorem regular_family_C2_pullback_of_open {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hO : IsOpen (bdry s)ᶜ)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) := by
  have key := GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.proof A' A h hh (bdry s)ᶜ hO phT ph
    (ph ∘ h) hph (fun _ _ => rfl) hT (fun k K hK hKs => hC k K hKs hK)
  intro j K hKs hK
  exact key j K hK hKs

end

end GlobalTheory.CompanionTheory.Ar.Giv
