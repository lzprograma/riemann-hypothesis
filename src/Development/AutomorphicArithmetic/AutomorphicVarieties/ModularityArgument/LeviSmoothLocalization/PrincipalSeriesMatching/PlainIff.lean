module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.Bridge
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.LocalFields.UnramifiedHensel
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

@[expose] public section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem valuation_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact le_antisymm (le_uniformizer_iff.2 h1) (hy ▸ h2 y (hy ▸ uniformizer_lt_one))

private theorem absPow_one_unif :
    ((absPow k 1 (unif k) : ℂˣ) : ℂ) * (resCard k : ℂ) = 1 := by
  have hq : (resCard k : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
    exact_mod_cast this.ne'
  rw [val_absPow, Complex.cpow_one, GlobalTheory.GLDoubling.nabs_unif valuation_unif]
  push_cast
  exact inv_mul_cancel₀ hq

private theorem link_iff {ξ ξ' : kˣ →* ℂˣ} (hξ : IsSmoothChar ξ) (hξ' : IsSmoothChar ξ') :
    IrrGL.ofChar ξ hξ = (IrrGL.ofChar ξ' hξ').nu 1 ↔
      IsUnram (ξ' * ξ⁻¹) ∧ (((ξ' * ξ⁻¹) (unif k) : ℂˣ) : ℂ) = (resCard k : ℂ) := by
  have hA := absPow_one_unif (k := k)
  have hA0 : ((absPow k 1 (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
  constructor
  · rintro rfl
    have e : ξ' * (ξ' * absPow k 1)⁻¹ = (absPow k 1)⁻¹ := by
      rw [mul_inv, mul_inv_cancel_left]
    rw [e]
    refine ⟨isUnram_inv (isUnram_absPow k 1), ?_⟩
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have hq : (resCard k : ℂ) = ((absPow k 1 (unif k) : ℂˣ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hA
    rw [hq]
  · rintro ⟨hu, hv⟩
    obtain ⟨-, h2, -⟩ := polFacts k
    refine h2 ξ (ξ' * absPow k 1) ?_ ?_
    · have e : ξ * (ξ' * absPow k 1)⁻¹ = (ξ' * ξ⁻¹)⁻¹ * (absPow k 1)⁻¹ := by
        simp only [mul_inv, inv_inv]
        ac_rfl
      rw [e]
      exact isUnram_mul (isUnram_inv hu) (isUnram_inv (isUnram_absPow k 1))
    · refine Units.ext ?_
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] at hv
      rw [← hv] at hA
      rw [MonoidHom.mul_apply, Units.val_mul]
      have h0 : ((ξ (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp at hA
      rw [mul_comm, hA]

end Loc

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PlainIff := by
  intro K _ _ _ n hn π v
  obtain ⟨-, huniq, -, -, -⟩ := suppFacts K n hn π v
  have hq : (Ideal.absNorm v.asIdeal : ℂ) = (resCard (v.adicCompletion K) : ℂ) := by
    have h : GroundTheory.LocalField.residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal :=
      GroundTheory.Global.residueCard_adicCompletion
    rw [← h]
    rfl
  constructor
  · intro h
    refine ⟨fun σ hσ => ?_, fun s hs ξ hξ ξ' hξ' hu e => ?_⟩
    · obtain ⟨s, h1, h2, -⟩ := h σ hσ
      exact ⟨s, h1, h2⟩
    · obtain ⟨σ, hσ, -⟩ := id hs
      obtain ⟨t, ht, -, hl⟩ := h σ hσ
      obtain rfl : s = t := huniq s t hs ⟨σ, hσ, ht.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩
      obtain ⟨a, ha⟩ := hξ
      obtain ⟨b, hb⟩ := hξ'
      exact hl _ hb _ ha ((link_iff b a).2 ⟨hu, e.trans hq⟩)
  · rintro ⟨ht, hu⟩ σ hσ
    obtain ⟨s, hs, h1⟩ := ht σ hσ
    refine ⟨s, hs, h1, fun y hy z hz e => ?_⟩
    obtain ⟨ξ, hξ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y (h1 y hy)
    obtain ⟨ξ', hξ', rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar z (h1 z hz)
    obtain ⟨h2, h3⟩ := (link_iff hξ hξ').1 e
    exact hu s ⟨σ, hσ, hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩ ξ' ⟨hξ', hz⟩ ξ ⟨hξ, hy⟩ h2 (h3.trans hq.symm)
