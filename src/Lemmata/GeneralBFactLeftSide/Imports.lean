module

public import Lemmata.GeneralBFactRightBisForm.Imports
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace Bl.general_b_fact_left'''''

theorem goal1 {O A I : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Fintype I] [DecidableEq I] {B : I → Type} [(i : I) → AddCommGroup (B i)]
    [(i : I) → Module O (B i)] (ε : (i : I) → B i →ₗ[O] A) (T : (i : I) → Set (B i)) :
    Submodule.span O {X : A | ∃ F : (i : I) → B i,
      (∀ i, F i ∈ Submodule.span O (T i)) ∧ X = ∏ i, ε i (F i)} =
    Submodule.span O {X : A | ∃ F : (i : I) → B i,
      (∀ i, F i ∈ T i) ∧ X = ∏ i, ε i (F i)} := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    refine Bl.general_b_fact_right_bis_form.goal1 ε T _ ?_ F hF
    exact fun G hG => Submodule.subset_span ⟨G, hG, rfl⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun i => Submodule.subset_span (hF i), rfl⟩

end Bl.general_b_fact_left'''''
