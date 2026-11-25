module

import Development.WeilBound.CoreStatements.VolumeEquality.RegularFunctionChartAdjoin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Mathlib.Tactic.Linter.Style

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordLoc

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hξ : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hξ).hom f) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have h2 := congrArg (fun g => g.hom f) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes q.2).hom
    ((X.presheaf.germ U q.1 hq).hom f)) = _
  rw [h2]

end GlobalTheory.CompanionTheory.Ar.CoordLoc

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_iff_exists_chart_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  apply SheetDecomposition.regular_function_chart_adjoin

end GlobalTheory.CompanionTheory.Ar
