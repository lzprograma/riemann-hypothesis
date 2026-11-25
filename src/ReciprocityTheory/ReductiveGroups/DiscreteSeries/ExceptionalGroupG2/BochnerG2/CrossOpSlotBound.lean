module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SltEqZeroOfCompact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpSlotBound

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Slot

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem position_perp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} (i : Fin k) {P : Big n k M} (hP : P ∈ ncV ε V k)
    (hperp : ∀ F ∈ ncV ε V k, (∀ κ, slice i κ F ∈ Wm ε E V) → inner ℂ F P = 0) :
    ∀ κ, slice i κ P ∈ Wp ε E V :=
  DS.position_perp_of hU i hP (fun _ hx => ncV_one_decomp hE hU hV hmono hh hbig hx) hperp

theorem crossOp_position_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} (i : Fin k) {P : Big n k M} (hP : ∀ κ, slice i κ P ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖P‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) :=
  DS.crossOp_position_bound_of i hP (fun _ hx => Wp_bound hE hU hV hmono hh hbig hx)

end Slot

end ReciprocityTheory.ChartRestriction.DS.G2
