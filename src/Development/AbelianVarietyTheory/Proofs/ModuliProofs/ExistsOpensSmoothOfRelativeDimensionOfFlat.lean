module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionAndGeometricallyConnect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM


namespace GlobalTheory.ProperFlatNearFibre

theorem exists_opens_smoothOfRelativeDimension_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}}
    (s : Z ⟶ Spec R) [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  apply GlobalTheory.SmoothNearFibre.exists_opens_of_flat <;> assumption

theorem smoothOfRelativeDimension_pullback_snd {Z T S : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S)
    (g : ℕ) (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → (pullback s t).Opens :=
    fun W => pullback.fst s t ⁻¹ᵁ W.1
  have htop : iSup V = ⊤ := by
    rw [← top_le_iff]
    intro y _
    obtain ⟨W, hW, hW'⟩ := h (pullback.fst s t y) (pullback.snd s t y) (by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
    fun W => ?_
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{0} g)
    ((isPullback_morphismRestrict (pullback.fst s t) W.1).paste_vert
      (IsPullback.of_hasPullback s t)) W.2

theorem exists_away_smoothOfRelativeDimension :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s g K _ x hs hf h
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := ⨆ W : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)}, W.1
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  let w : Sp K := (default : PrimeSpectrum K)
  have hp : spMap x w ∈ (s '' (U : Set Z)ᶜ)ᶜ := by
    rintro ⟨z, hz, e⟩
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_flat s (spMap x) g h z w e
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩)
  obtain ⟨_, ⟨f, rfl⟩, hf1, hf2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp
      hc.isOpen_compl
  refine ⟨f, ?_, smoothOfRelativeDimension_pullback_snd _ _ g fun z y e => ?_⟩
  · have h1 : f ∉ (spMap x w).asIdeal := hf1
    rwa [GlobalTheory.VeryDenseFibres.spMap_apply_asIdeal, RingHom.mem_ker] at h1
  · have h1 : s z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨y, e.symm⟩
    have h2 : z ∈ U := by
      by_contra hz
      exact hf2 h1 ⟨z, hz, rfl⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩

end GlobalTheory.ProperFlatNearFibre
