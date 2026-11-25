module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

open UpperTheory.V.Z.Sym.Al

private theorem exists_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ s : kˣ, valuation k (s : k) < 1 := by
  obtain ⟨x, hx0, hx⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  exact ⟨Units.mk0 x (fun h => hx0 (by simp [h])), hx⟩

private theorem split_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : ∃ s t : kˣ, valuation k (s : k) < 1 ∧ valuation k (t : k) < 1 ∧ x = s / t := by
  obtain ⟨p, hp⟩ := exists_small k
  by_cases hx : valuation k (x : k) < 1
  · refine ⟨x * p, p, ?_, hp, by simp⟩
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hp
  · refine ⟨p, p * x⁻¹, hp, ?_, by simp⟩
    have h1 : 1 ≤ valuation k (x : k) := not_lt.1 hx
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    have h0 : valuation k (x : k) ≠ 0 := by simp
    have h2 : (valuation k (x : k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hp

theorem UpperTheory.V.Z.Sym.Al.unrSmooth :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ χ : kˣ →* ℂˣ, (∀ u ∈ Hi.Uo k, χ u = 1) → IsSmoothChar χ) ∧
        ∀ (ψ : Fin 2 → kˣ →* ℂˣ) (b : kˣ →* ℂˣ), (∀ t : kˣ, valuation k (t : k) < 1 → expo ψ ![t, t⁻¹] = expo ![b, 1] ![t, t⁻¹]) → ψ 0 / ψ 1 = b := by
  intro k _ _ _ _
  refine ⟨fun χ h => isSmoothChar_of_isUnram fun x hx => h x hx, fun ψ b h => ?_⟩
  have key : ∀ t : kˣ, valuation k (t : k) < 1 → (ψ 0 / ψ 1) t = b t := by
    intro t ht
    have h1 := Units.val_injective (h t ht)
    have h2 := mul_right_cancel h1
    rw [torusChar_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two] at h2
    simpa [MonoidHom.div_apply, div_eq_mul_inv] using h2
  refine MonoidHom.ext fun x => ?_
  obtain ⟨s, t, hs, ht, rfl⟩ := split_small k x
  rw [map_div, map_div, key s hs, key t ht]
