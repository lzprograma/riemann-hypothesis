module

import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

def DGamSmooth {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (p : ℕ), p.Prime → p ∣ ((Fm.D x i).mem u).C.DGam →
    p ≤ 2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1

theorem Closed.sub {𝒞 𝒞' : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P)
    (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm) : Closed 𝒞' P := by
  obtain ⟨e1, he1, h1⟩ := h
  refine ⟨e1, he1, fun eps h0 hle => ?_⟩
  obtain ⟨K, hK⟩ := h1 eps h0 hle
  exact ⟨K, fun Fm CH hc hL => hK Fm CH (hs Fm hc) hL⟩

theorem Closed.of_class {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop}
    (hs : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 𝒞 Fm → P Fm CH) : Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc _ => hs Fm CH hc⟩⟩

theorem Closed.large {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (K0 : TransportedAlt) (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), Fm.Large K0 CH → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  apply Formalism.MainNotions.S.closed_of_large <;> assumption

end Formalism.MainNotions.Pk

end
