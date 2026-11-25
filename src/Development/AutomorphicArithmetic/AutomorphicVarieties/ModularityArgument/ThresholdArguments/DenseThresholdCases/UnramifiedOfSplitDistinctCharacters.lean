module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

@[expose] public section




section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.unramified_of_split_distinct_characters :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ), IsSplitAt w → CompSub π w ψ →
        (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) → (∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow (Kw w) 1) → IsUnramU π w := by
  intro H L _ _ _ n π w ψ hw hc hu hne
  obtain ⟨hsm, τ, ⟨-, f, hf0, hfπ, hf⟩, hsq⟩ := hc
  obtain ⟨hs1, hs2, -, -⟩ := secSpec L n w hw
  have hker : ∀ x, f x = 0 → x = 0 := by
    let S : Subrepresentation τ.ρ := ⟨LinearMap.ker f, by
      intro g x hx
      have h := hf ⟨secW n w g, hs1 g⟩ x
      have h' : f (τ.ρ g x) = RU L n (secW n w g) (f x) := by
        rw [← h]
        show f (τ.ρ g x) = f (τ.ρ (cLoc w (secW n w g)) x)
        rw [hs2 g]
      rw [LinearMap.mem_ker] at hx ⊢
      rw [h', hx, map_zero]⟩
    have hS : S = ⊥ := by
      rcases (τ.irred.eq_bot_or_eq_top S) with h | h
      · exact h
      · refine absurd (LinearMap.ext fun x => ?_) hf0
        have : x ∈ S.toSubmodule := by rw [h]; trivial
        exact this
    intro x hx
    have : x ∈ S.toSubmodule := hx
    rw [hS] at this
    exact this
  obtain ⟨ω, rfl, hω⟩ : ∃ ω : Fin n → (Kw w)ˣ →* ℂˣ,
      ψ = (fun i => ω i * absPow (Kw w) (((n : ℂ) - 1) / 2)) ∧ ∀ i, IsSmoothChar (ω i) := by
    refine ⟨fun i => ψ i * absPow (Kw w) (-(((n : ℂ) - 1) / 2)), funext fun i => ?_,
      fun i => (hsm i).mul (isSmoothChar_of_isUnram (isUnram_absPow _ _))⟩
    have h0 : absPow (Kw w) 0 = 1 := by
      ext x
      simp [absPow]
    rw [mul_assoc, ← absPow_add, neg_add_cancel, h0, mul_one]
  have hneω : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (Kw w) 1 := fun i j hij =>
    ⟨fun h => (hne i j hij).1 (by simp only [h]), fun h => (hne i j hij).2 (by
      simp only []
      rw [h, mul_right_comm])⟩
  have hE : Nonempty (τ.ρ.Equiv (UpperTheory.V.Hi.PS ω)) :=
    (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient H (Kw w) n ω hω hneω).2 _ τ.ρ τ.irred hsq
  obtain ⟨E⟩ := hE
  obtain ⟨v₀, hv₀, hfix⟩ := locSph (Kw w) n _ hu
  obtain ⟨v, rfl⟩ := E.surjective v₀
  have hv : v ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero E)
  have hτ : ∀ u ∈ KO (Kw w) (Fin n), τ.ρ u v = v := fun u hu' => by
    apply E.injective
    have h1 := LinearMap.congr_fun (E.isIntertwining' u) v
    exact h1.trans (hfix u hu')
  refine ⟨f v, hfπ v, fun h => hv (hker v h), fun x hx hK => ?_⟩
  have h := hf ⟨x, hx⟩ v
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL] at hK
  rw [← h]
  show f (τ.ρ (cLoc w x) v) = f v
  rw [hτ _ hK]
end
