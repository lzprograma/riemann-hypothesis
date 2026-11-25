module

import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem S_pos (X : Data E r) (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  apply GlobalTheory.sum_pnorm_w_sq_pos <;> assumption

theorem pnorm_contOn (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom := by
  apply GlobalTheory.Up.DivInFFPf.pnorm_contOn <;> assumption

theorem r_pos (X : Data E r) (Xa : ArchInM X) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have h := Xa.n_ge
    have h0 : nd X = 0 := by
      unfold nd
      rw [Fintype.card_eq_zero_iff]
      constructor
      rintro ⟨_, ⟨⟨a, _⟩, _⟩⟩
      exact a.elim0
    omega
  · exact hr

theorem lam_ne (X : Data E r) (Xa : ArchInM X) : ∃ v ∈ X.Λ, v ≠ 0 := by
  have hr := r_pos X Xa
  by_contra! h
  have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ := by
    rw [Submodule.span_le]
    intro v hv
    simp [h v hv]
  rw [X.Λ_span, top_le_iff] at h1
  have hm : (fun _ => (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
  rw [← h1, Submodule.mem_bot] at hm
  exact one_ne_zero (congrFun hm ⟨0, hr⟩)

end BigB

end ReciprocityTheory.ChartRestriction.G.AR.Up
