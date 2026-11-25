module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedHermitianSpace
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

noncomputable section
namespace GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace


open NumberField NumberField.IsCMField TensorProduct in
theorem _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj (E : Type) [Field E] [NumberField E] (cj : E → E)
    (h : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) (hne : ∃ z : E, cj z ≠ z) :
    IsCMField E := by
  let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  have inj := φ₀.injective
  have hadd : ∀ a b, cj (a + b) = cj a + cj b := fun a b =>
    inj (by rw [h, map_add (f := _), map_add (f := _), h, h, star_add])
  have hmul : ∀ a b, cj (a * b) = cj a * cj b := fun a b =>
    inj (by rw [h, map_mul, map_mul, h, h, star_mul'])
  have hinv : ∀ z, cj (cj z) = z := fun z => inj (by rw [h, h, star_star])
  let e : E ≃+* E :=
    { toFun := cj, invFun := cj, left_inv := hinv, right_inv := hinv,
      map_mul' := hmul, map_add' := hadd }
  let σ : E ≃ₐ[ℚ] E := e.toRatAlgEquiv
  have hσ : ∀ z, σ z = cj z := fun _ => rfl
  have hsq : σ ^ 2 = 1 := AlgEquiv.ext fun z => by
    rw [pow_two, AlgEquiv.mul_apply, hσ, hσ, hinv, AlgEquiv.one_apply]
  have hne1 : σ ≠ 1 := by
    obtain ⟨z, hz⟩ := hne
    intro h1
    exact hz (by rw [← hσ, h1, AlgEquiv.one_apply])
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne1
  have hfix : ∀ x, x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ cj x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun hx => hx σ (Subgroup.mem_zpowers σ), fun hx f hf => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    clear hf
    have hσx : σ x = x := hx
    have hσx' : σ⁻¹ x = x := by
      calc σ⁻¹ x = (σ⁻¹ * σ) x := by rw [AlgEquiv.mul_apply, hσx]
        _ = x := by rw [inv_mul_cancel, AlgEquiv.one_apply]
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσx, ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hσx', ih]
  have hS : maximalRealSubfield E =
      (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield := by
    ext x
    rw [mem_maximalRealSubfield_iff, IntermediateField.mem_toSubfield, hfix]
    exact ⟨fun hx => inj ((h φ₀ x).trans (hx φ₀)), fun hx φ => by rw [← h φ x, hx]⟩
  have hfin : Module.finrank (maximalRealSubfield E) E = 2 := by
    rw [hS]
    exact (IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)).trans
      (by rw [Nat.card_zpowers, hord])
  haveI : IsTotallyComplex E := ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hv
    obtain ⟨z, hz⟩ := hne
    exact hz (v.embedding.injective ((h _ z).trans (RingHom.congr_fun hv z)))⟩
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield E) E := ⟨hfin⟩
  exact ⟨⟩


open NumberField NumberField.IsCMField TensorProduct in
theorem _root_.GlobalTheory.LeastExponentCompare.conj_iff (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by
  constructor
  · rintro ⟨h, hne⟩
    haveI := _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj E cj h hne
    refine ⟨this, funext fun z => ?_⟩
    let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
    exact φ₀.injective (by rw [h, complexEmbedding_complexConj, RCLike.star_def])
  · rintro ⟨_, rfl⟩
    refine ⟨fun φ z => by rw [complexEmbedding_complexConj, RCLike.star_def], ?_⟩
    by_contra! hall
    exact complexConj_ne_one E (AlgEquiv.ext hall)

section AtLattice
variable (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

variable [IsCMField E]

end AtLattice

section Families

abbrev SpaceRule : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Bil Y)

abbrev ValueRule (S : SpaceRule) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

variable {S : SpaceRule} {φ : ValueRule S}

end Families

end GlobalTheory.LeastExponentCompare
