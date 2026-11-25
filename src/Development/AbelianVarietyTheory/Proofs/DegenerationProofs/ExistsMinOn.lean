module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModK
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
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
import Mathlib.GroupTheory.IndexNSmul
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis.AdaptedFamily

theorem exists_min_on {X : Type} {Q : X → ℤ} (h : ∀ x, 0 ≤ Q x) {s : Set X} (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, Q x ≤ Q y := by
  obtain ⟨x, hx, hm⟩ := (wellFounded_lt (α := ℕ)).has_min ((fun x => (Q x).toNat) '' s) (hs.image _)
  obtain ⟨x, hx, rfl⟩ := hx
  refine ⟨x, hx, fun y hy => ?_⟩
  have h₁ : ¬ (Q y).toNat < (Q x).toNat := hm _ ⟨y, hy, rfl⟩
  have h₂ := h x
  have h₃ := h y
  omega

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (i : Fin r), ∃ s : Fam D.toPre F k, GlobalTheory.ZH.FamOf D.toPre F (f i) s := by
  classical
  intro hL V _ _ _ ϖ hϖ D Q hQ k hk
  have hQ0 : ∀ χ, 0 ≤ Q χ := fun χ => by
    by_cases h : χ = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ h; omega
  let C := D.toPre.X ⧸ FamFree.multiples D.toPre k
  have hc : Nat.card C = k ^ Module.finrank ℤ D.toPre.X := AddSubgroup.index_range_nsmul D.toPre.X k
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite C
  let e : Fin (Fintype.card (C × Fin (k ^ D.toPre.P.g))) ≃ C × Fin (k ^ D.toPre.P.g) := (Fintype.equivFin _).symm
  choose rep hrep hmin using fun c : C => exists_min_on hQ0
    (s := {α | (QuotientAddGroup.mk α : C) = c}) ⟨c.out, c.out_eq⟩
  have hQmin : ∀ c z, Q (rep c) ≤ Q (rep c + k • z) := fun c m =>
    hmin c _ (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, rfl⟩).symm.trans (hrep c))
  choose b hb using fun c => AdaptedBasis.exists_isBasisB hL.2.1.secTwist D.toPre hk (rep c)
  choose Φ f hΦ hf hz using fun c m =>
    AdaptedBasis.integralFamily_of_min hL.1.globalFns hϖ hQ hk (rep c) (b c m) (hQmin c)
  have inj : ∀ c c', rep c = rep c' → c = c' := fun c c' h => (hrep c).symm.trans (by rw [h]; exact hrep c')
  let ε : ∀ i₀, {i // rep (e i).1 = rep (e i₀).1} ≃ Fin (k ^ D.toPre.P.g) := fun i₀ =>
    { toFun := fun i => (e i.1).2
      invFun := fun m => ⟨e.symm ((e i₀).1, m), by rw [Equiv.apply_symm_apply]⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_eq.2 (Prod.ext (inj _ _ i.2).symm rfl))
      right_inv := fun m => by simp }
  refine ⟨_, fun i => rep (e i).1, k ^ D.toPre.P.g, fun i => f (e i).1 (e i).2,
    ⟨⟨fun i => hQmin _, fun i i' ⟨m, hm⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩, fun i => ⟨_, hΦ _ _⟩, fun i => hz _ _,
      fun i₀ => ?_⟩, fun F _ _ i => FamBaseChange.main hL.1.globalFns V _ D k _ _ (hΦ _ _) F⟩
  · exact congrArg rep ((hrep _).symm.trans (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, hm.symm⟩).symm.trans (hrep _)))
  · obtain ⟨m, hm⟩ := (FamFree.mk_eq_mk_iff _ _).1 (hrep (QuotientAddGroup.mk α))
    refine ⟨e.symm (QuotientAddGroup.mk α, ⟨0, by positivity⟩), m, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hm.symm
  · exact (Nat.card_congr (ε i₀)).trans (Nat.card_fin _)
  · refine AdaptedBasis.isBasisB_reindex (ε i₀) (hb (e i₀).1) fun i => ?_
    have key : ∀ c c' m, c = c' → f c m (rep c') = b c' m := by
      rintro c _ m rfl; exact hf c m
    exact key _ _ _ (inj _ _ i.2)

end GlobalTheory.OneBasis.AdaptedFamily
