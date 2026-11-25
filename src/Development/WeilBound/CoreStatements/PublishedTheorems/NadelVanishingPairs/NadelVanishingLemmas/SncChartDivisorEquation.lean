module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorMultCharacterize
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

noncomputable section

namespace GlobalTheory.Discrepancy.MonoEqn

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

def ordU (v : Y) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Scheme.ord (g : Y.functionField) v)
  map_one' := by
    have h := Scheme.ord_mul (x := v) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [mul_one] at h
    have h0 : Scheme.ord (1 : Y.functionField) v = 0 := by omega
    simp [h0]
  map_mul' f g := by
    simp [Units.val_mul, Scheme.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

theorem ord_prod_zpow {ι : Type} (J : Finset ι) (u : ι → Y.functionFieldˣ) (m : ι → ℤ) (v : Y) :
    Scheme.ord ((∏ j ∈ J, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v =
      ∑ j ∈ J, m j * Scheme.ord (u j : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_prod (ordU (Y := Y) v) (fun j => u j ^ m j) J)
  rw [toAdd_prod] at h
  calc Scheme.ord ((∏ j ∈ J, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v
      = Multiplicative.toAdd (ordU v (∏ j ∈ J, u j ^ m j)) := rfl
    _ = ∑ j ∈ J, Multiplicative.toAdd (ordU v (u j ^ m j)) := h
    _ = ∑ j ∈ J, m j * Scheme.ord (u j : Y.functionField) v := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

end GlobalTheory.Discrepancy.MonoEqn

open GlobalTheory.Discrepancy.MonoEqn in
theorem GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ D : CartierDiv Y, D.supp ≤ B → D.IsEqn y (∏ j ∈ J, u j ^ D.mult (w j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc D hD
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth q
  obtain ⟨_, _, _, hEqn⟩ := MultEff.eff_supp_eq_of_mult Y D
  apply hEqn
  intro v hv
  rw [ord_prod_zpow]
  by_cases hex : ∃ j ∈ J, v = w j
  · obtain ⟨j0, hj0, rfl⟩ := hex
    rw [Finset.sum_eq_single j0]
    · rw [hc.ord_self j0 hj0, mul_one]
    · intro j hj hne
      rw [hc.ord_other j hj (w j0) hv (fun heq => hne (hc.inj hj hj0 heq.symm)), mul_zero]
    · intro h'
      exact absurd hj0 h'
  · have h0 : D.mult v = 0 := by
      by_contra hne
      exact hex ((hc.mem v hv (CartierDiv.coheight_eq_one_of_mult_ne_zero hne)).mp
        (hD (CartierDiv.mem_supp_of_mult_ne_zero hne)))
    rw [h0]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [hc.ord_other j hj v hv (fun heq => hex ⟨j, hj, heq⟩), mul_zero]
