module

public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.SChain

@[expose] public section

noncomputable section

open Formalism Formalism.D5
open Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.LChain

namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds

variable {U0 : Type} [Fintype U0]
  {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}

/-- The prime-power/divisibility side of inequality (M), at a fixed translate `u0`.

In the source development this is the `ASK` component of `Data`. Under `LChain.Ident`,
it is identified with the explicit sum of the character-class prime-power contributions.
-/
def P_u (D : Data U0 W Top m f) (u0 : U0) : ℝ := D.ASK u0

/-- The main term on the right-hand side of inequality (M), at a fixed translate. -/
def M_u (D : Data U0 W Top m f) (u0 : U0) : ℝ := D.Main u0

/-- The fully expanded error term used by the existing Lean proof of inequality (M). -/
def E_u (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (u0 : U0) : ℝ :=
  ErrX5at D C Xpp u0

/-- **Inequality (M), pointwise explicit-error form.**

For every translate `u0`, the prime-power sum is bounded by the main term plus the
source development's explicit error `ErrX5at`. This theorem is a named interface to
`each_unit_bound_statement`; it introduces no new mathematical assumptions and does
not replace the explicit remainder by the paper's later compressed `x^(...) * 𝔈`
notation.
-/
theorem inequality_M_pointwise
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (hS : D.HidaSetting C)
    (hDIV : D.DIV C)
    (hE : EComp5 D C)
    (hH : D.HComp C)
    (hCount : Count5 D C)
    (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : LossBounds D C)
    (hSI : D.SlopeIneq)
    (hHH : D.HHBound C)
    (hFP : D.FParams) :
    ∀ u0, P_u D u0 ≤ M_u D u0 + E_u D C Xpp u0 := by
  intro u0
  exact each_unit_bound_statement D C Xpp hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP u0

/-- The finite mean of the pointwise inequality (M), over the translate index type.

This is the averaged consequence of the pointwise theorem. `U0` must be nonempty so
that its cardinality is a valid positive normalizing denominator.
-/
theorem inequality_M_average
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (hU : Nonempty U0)
    (hS : D.HidaSetting C)
    (hDIV : D.DIV C)
    (hE : EComp5 D C)
    (hH : D.HComp C)
    (hCount : Count5 D C)
    (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : LossBounds D C)
    (hSI : D.SlopeIneq)
    (hHH : D.HHBound C)
    (hFP : D.FParams) :
    (∑ u0 : U0, (P_u D u0 - M_u D u0)) / (Fintype.card U0 : ℝ) ≤
      (∑ u0 : U0, E_u D C Xpp u0) / (Fintype.card U0 : ℝ) := by
  have hsum :
      (∑ u0 : U0, (P_u D u0 - M_u D u0)) ≤
        ∑ u0 : U0, E_u D C Xpp u0 := by
    apply Finset.sum_le_sum
    intro u0 _
    have hpoint :=
      inequality_M_pointwise D C Xpp hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP u0
    change D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0 at hpoint
    change D.ASK u0 - D.Main u0 ≤ ErrX5at D C Xpp u0
    linarith
  have hcard : (0 : ℝ) < (Fintype.card U0 : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hU)
  have hinv : 0 ≤ ((Fintype.card U0 : ℝ)⁻¹) := inv_nonneg.mpr hcard.le
  calc
    _ = (∑ u0 : U0, (P_u D u0 - M_u D u0)) * ((Fintype.card U0 : ℝ)⁻¹) := by
      rw [div_eq_mul_inv]
    _ ≤ (∑ u0 : U0, E_u D C Xpp u0) * ((Fintype.card U0 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hsum hinv
    _ = _ := by rw [div_eq_mul_inv]

/-- Under the explicit source identification, `P_u` is the sum of the original
character-class prime-power contributions used in the construction.
-/
theorem P_u_eq_character_sum
    {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ}
    (Ddata : Data H W Top m f)
    (A : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H))
    (hIdent : Ident Ddata A N ell TT a w eT eP)
    (u0 : H) :
    P_u Ddata u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK A N (a t) t (w u0 j) := by
  change Ddata.ASK u0 = _
  rcases hIdent with ⟨_, _, _, _, hASK⟩
  exact hASK u0

end Formalism.LFunctionChainParameters.WeightedSlopeBounds

end
