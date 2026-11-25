module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.ChiGrid

theorem exists_ringEquiv_mem_iff_star {E : Type} [Field E] [NumberField E] [StarRing E] :
    ∃ σ : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E,
      ∀ (a : FractionalIdeal (𝓞 E)⁰ E) (x : E), x ∈ σ a ↔ star x ∈ a := by
  let τ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut : E ≃+* E)
  have hτ : ∀ x : E, IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) τ x = star x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, star_div₀]
    rfl
  refine ⟨FractionalIdeal.ringEquivOfRingEquiv E E τ, fun a x => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg star (hτ y)).trans (star_star y)
    exact h.symm ▸ hy
  · exact ⟨star x, h, (hτ (star x)).trans (star_star x)⟩

theorem stairId_ne_zero_and_mem_rev_iff : ∀ (D : D7) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → ∀ (c : ℕ) (p : Fin c), stairId 𝔞 𝔞' c p ≠ 0 ∧ ∀ x, x ∈ stairId 𝔞 𝔞' c p.rev ↔ star x ∈ (stairId 𝔞 𝔞' c p)⁻¹ := by
  intro D 𝔞 𝔞' h0 h c p
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_mem_iff_star (E := D.host.E)
  have h1 : σ 𝔞 = 𝔞' := by
    ext x
    rw [hσ, h]
  have h2 : σ 𝔞' = 𝔞 := by
    ext x
    rw [hσ, h, star_star]
  have h0' : 𝔞' ≠ 0 := h1 ▸ (map_ne_zero_iff _ σ.injective).2 h0
  refine ⟨mul_ne_zero (pow_ne_zero _ h0) (inv_ne_zero (pow_ne_zero _ h0')), fun x => ?_⟩
  have h3 : σ (stairId 𝔞' 𝔞 c p.rev) = stairId 𝔞 𝔞' c p.rev := by
    unfold stairId
    rw [map_mul, map_inv₀, map_pow, map_pow, h1, h2]
  rw [← stairId_rev, ← hσ, h3]

end GlobalTheory.ChiGrid
