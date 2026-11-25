module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbTransport

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
theorem _root_.GlobalTheory.Mass.OrbTransport.main : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → _root_.GlobalTheory.Mass.orbSum G X (fun x => N (f x)) = _root_.GlobalTheory.Mass.orbSum G' Y N := by
  intro G G' α β _ _ _ _ φ f X Y N hX hY hf hequiv hN
  have hcard : ∀ x ∈ X, ENat.card (stabilizer G' (f x)) = ENat.card (stabilizer G x) := by
    intro x hx
    refine (ENat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun g => ?_)).symm
    simp only [mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← hequiv g x hx]
    exact ⟨fun h => by rw [h], fun h => hf.injOn (hX g x hx) hx h⟩
  have hout : ∀ q : {q : orbitRel.Quotient G α // q.out ∈ X},
      (Quotient.mk (orbitRel G' β) (f q.1.out)).out ∈ Y := by
    intro q
    obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G' β) (f q.1.out)
    rw [← hg]
    exact hY g _ (hf.mapsTo q.2)
  let F : {q : orbitRel.Quotient G α // q.out ∈ X} → {q : orbitRel.Quotient G' β // q.out ∈ Y} :=
    fun q => ⟨Quotient.mk _ (f q.1.out), hout q⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
      obtain ⟨g', hg'⟩ := Quotient.exact (congrArg Subtype.val h)
      apply Subtype.ext
      show q₁ = q₂
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      apply Quotient.sound
      refine ⟨φ.symm g', ?_⟩
      apply hf.injOn (hX _ _ h₂) h₁
      rw [hequiv _ _ h₂, MulEquiv.apply_symm_apply]
      exact hg'
    · rintro ⟨q', hq'⟩
      obtain ⟨x, hx, hfx⟩ := hf.surjOn hq'
      obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G α) x
      have hmem : (Quotient.mk (orbitRel G α) x).out ∈ X := by rw [← hg]; exact hX g x hx
      refine ⟨⟨Quotient.mk _ x, hmem⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (f (Quotient.mk (orbitRel G α) x).out) = q'
      rw [← Quotient.out_eq q', ← hg, hequiv g x hx, hfx]
      exact Quotient.sound ⟨φ g, rfl⟩
  unfold _root_.GlobalTheory.Mass.orbSum
  rw [← (Equiv.ofBijective F hF).tsum_eq]
  congr 1
  funext q
  obtain ⟨g', hg'⟩ := Quotient.mk_out (s := orbitRel G' β) (f q.1.out)
  show _ = (ENat.card (stabilizer G' (Quotient.mk (orbitRel G' β) (f q.1.out)).out) : ℝ≥0∞)⁻¹ *
    N (Quotient.mk (orbitRel G' β) (f q.1.out)).out
  rw [← hg', ← ENat.card_congr (stabilizerEquivStabilizer (g := g') rfl).toEquiv,
    hN, hcard _ q.2]

end GlobalTheory.Mass.OrbTransport
