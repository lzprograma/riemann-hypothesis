module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredElements

theorem preservesFilteredColimits_modules_iff_elements :
    ∀ (Λ : Type 1) [Ring Λ] (N : CommRingCat.{0} ⥤ ModuleCat.{1} Λ), (PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})) ∧ (PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, (N.map (c.ι.app j)).hom y = x) ∧ ∀ j (y : N.obj (D.obj j)), (N.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (N.map (D.map f)).hom y = 0) := by
  intro Λ _ N
  have hP : PreservesColimitsOfSize.{0, 0} (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 1, 0, 0} Λ
  have h1 : PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) := by
    constructor
    · intro h
      exact comp_preservesFilteredColimits N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
    · intro h
      constructor
      intro J _ _
      constructor
      intro K
      exact preservesColimit_of_reflects_of_preserves N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
  refine ⟨h1, ?_⟩
  rw [h1, _root_.GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements]
  rfl

end GlobalTheory.EtC.FilteredElements
