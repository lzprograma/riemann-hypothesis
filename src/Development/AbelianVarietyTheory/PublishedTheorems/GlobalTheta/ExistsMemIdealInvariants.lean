module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Published

def idealInvariants (K : Type) [Field K] [NumberField K] [Algebra K ℂ] : Set ℂ :=
  {x | ∃ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair),
    IsIdealLattice 𝔟 L ∧ (latticeCurve L).j = x}

def IdealInvariantsOneOrbitSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair), IsIdealLattice 𝔞 L →
      IsAlgebraic K (latticeCurve L).j ∧
      MulAction.orbit (ℂ ≃ₐ[K] ℂ) (latticeCurve L).j = idealInvariants K

theorem ComplexMultiplicationJSt.oneOrbit (h : ComplexMultiplicationJSt) :
    IdealInvariantsOneOrbitSt := by
  intro K _ _ _ _ h2 𝔞 L hL
  obtain ⟨H, art, hH, -, hgen, hact⟩ := h K h2
  have hjH : (latticeCurve L).j ∈ H := by
    rw [← hgen 𝔞 L hL]
    exact IntermediateField.mem_adjoin_simple_self K _
  have : FiniteDimensional K H := hH.1.1
  have : IsAbelianGalois K H := hH.1.2.1
  refine ⟨?_, ?_⟩
  · have hx : IsIntegral K (⟨_, hjH⟩ : H) := IsIntegral.of_finite K _
    exact (IntermediateField.isIntegral_iff.mp hx).isAlgebraic
  · ext x
    constructor
    · rintro ⟨ρ, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, ClassGroup.mk K c = art.symm (ρ.restrictNormal H) :=
        ClassGroup.induction (R := 𝓞 K) K (P := fun d => ∃ c, ClassGroup.mk K c = d)
          (fun c => ⟨c, rfl⟩) _
      obtain ⟨L', hL'⟩ := exists_isIdealLattice h2 (c⁻¹ * 𝔞)
      refine ⟨c⁻¹ * 𝔞, L', hL', ?_⟩
      have key := hact 𝔞 c L L' hL hL' ⟨_, hjH⟩ rfl
      rw [hc, art.apply_symm_apply] at key
      show _ = ρ (latticeCurve L).j
      rw [← key]
      exact AlgEquiv.restrictNormal_commutes ρ H ⟨_, hjH⟩
    · rintro ⟨𝔠, L'', hc, rfl⟩
      obtain ⟨ρ, hρ⟩ :=
        GlobalTheory.GaloisDescent.exists_algEquiv_extend (L := ℂ) (art (ClassGroup.mk K (𝔞 * 𝔠⁻¹)))
      refine ⟨ρ, ?_⟩
      have hL'' : IsIdealLattice ((𝔞 * 𝔠⁻¹)⁻¹ * 𝔞) L'' := by
        rwa [show (𝔞 * 𝔠⁻¹)⁻¹ * 𝔞 = 𝔠 by group]
      show ρ (latticeCurve L).j = _
      rw [← hact 𝔞 _ L L'' hL hL'' ⟨_, hjH⟩ rfl]
      exact hρ ⟨_, hjH⟩

end GlobalTheory.Published
