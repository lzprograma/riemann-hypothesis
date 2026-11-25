module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

noncomputable section

namespace GlobalTheory.OpenDim

theorem ringKrullDim_affineOpen (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ d : ℕ, ringKrullDim Γ(Y, U) = d ∧ Algebra.trdeg F Y.functionField = d := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcomp : φ ≫ Y.presheaf.germ U _ hη =
      Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_preimage, ← hU.fromSpecStalk_eq_fromSpecStalk hη,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower F Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congr($(hcomp).hom a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul F Γ(Y, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(Y, U)).injective
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  exact ⟨d, h₁, (trdeg_eq_of_isAlgebraic_top F Γ(Y, U) Y.functionField).trans h₂⟩

theorem topologicalKrullDim_open (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] (V : Y.Opens) (hne : (V : Set Y).Nonempty) :
    topologicalKrullDim (V : Set Y) = topologicalKrullDim Y := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra

  have chart : ∀ (V : Y.Opens) (x : Y), x ∈ V → ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V :=
    fun _ _ hx ↦ exists_isAffineOpen_mem_and_subset hx
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨U₀, hU₀, hx₀U₀, -⟩ := chart V x₀ hx₀
  obtain ⟨d₀, -, hd₀⟩ := ringKrullDim_affineOpen F f hU₀ ⟨x₀, hx₀U₀⟩
  have affDim : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      topologicalKrullDim (U : Set Y) = d₀ := fun U hU hUne ↦ by
    obtain ⟨d, h₁, h₂⟩ := ringKrullDim_affineOpen F f hU hUne
    obtain rfl : d = d₀ := by exact_mod_cast h₂.symm.trans hd₀
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have openDim : ∀ V : Y.Opens, (V : Set Y).Nonempty → topologicalKrullDim (V : Set Y) = d₀ :=
    fun V hV ↦ topologicalKrullDim_eq_of_forall_exists_isOpen hV fun x hx ↦ by
      obtain ⟨U, hU, hxU, hUV⟩ := chart V x hx
      refine ⟨U, U.isOpen, hxU, ?_⟩
      rw [Set.inter_eq_left.mpr hUV]
      exact affDim U hU ⟨x, hxU⟩
  have htop := openDim ⊤ ⟨x₀, trivial⟩
  rw [openDim V ⟨x₀, hx₀⟩, ← htop]
  exact (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Z := ((⊤ : Y.Opens) : Set Y)) (by simp))

theorem topologicalKrullDim_eq_of_isIso_restrict : ∀ (F : Type) [Field F] (W W' : Scheme.{0})
    [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W),
    LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens,
    (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  intro F _ W W' _ _ p q h hp hq _ U hU hiso
  have hsurj : Function.Surjective (h ∣_ U) := (h ∣_ U).surjective
  have e₁ : topologicalKrullDim (U : Set W) = topologicalKrullDim (h ⁻¹ᵁ U) := by
    refine topologicalKrullDim_eq_of_isEmbedding ((h ∣_ U) ≫ U.ι).isOpenEmbedding.isEmbedding ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
  have e₂ : topologicalKrullDim ((h ⁻¹ᵁ U : W'.Opens) : Set W') =
      topologicalKrullDim (h ⁻¹ᵁ U) :=
    topologicalKrullDim_eq_of_isEmbedding (h ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding
      (Scheme.Opens.range_ι _)
  have hne : ((h ⁻¹ᵁ U : W'.Opens) : Set W').Nonempty := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨y, -⟩ := hsurj ⟨u, hu⟩
    exact ⟨(h ⁻¹ᵁ U).ι y, by rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩⟩
  rw [← topologicalKrullDim_open F q (h ⁻¹ᵁ U) hne, ← topologicalKrullDim_open F p U hU, e₁, e₂]

end GlobalTheory.OpenDim
