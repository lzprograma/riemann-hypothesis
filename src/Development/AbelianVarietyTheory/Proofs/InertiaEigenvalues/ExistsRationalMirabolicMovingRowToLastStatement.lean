module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLast
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a → ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧ ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  first | exact @GlobalTheory.CuspGeneric.mir_exists_row
