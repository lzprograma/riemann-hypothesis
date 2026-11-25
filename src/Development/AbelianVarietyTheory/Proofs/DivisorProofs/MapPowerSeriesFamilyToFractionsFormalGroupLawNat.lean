module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySum
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem constantCoeff_nmul_zero {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  apply _root_.GlobalTheory.QLog.NmulSubst.constantCoeff_nmul <;> assumption

theorem up_nmul : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  intro R S _ _ _ d μ hμ n
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact constantCoeff_nmul_zero μ hμ n j
      | inr j => simp
    funext i
    show map (algebraMap R S) ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = (fun v : Fin d → MvPowerSeries (Fin d) S => op (up S μ) v fun i => X i)^[n + 1]
      (fun _ => 0) i
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change map (algebraMap R S) (subst (Sum.elim (nmul μ n) fun i => X i) (μ i)) =
      subst (Sum.elim (nmul (up S μ) n) fun i => X i) (up S μ i)
    rw [map_subst (hasSubst_of_constantCoeff_zero h0), ← ih]
    congr 1
    funext j
    cases j with
    | inl j => rfl
    | inr j => simp

end GlobalTheory.QLog
