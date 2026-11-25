module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultPullbackRationalSectionPushforward
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy.MultIso

theorem ord_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  apply _root_.GlobalTheory.OrdPull.ord_ringEquiv <;> assumption

theorem ordFrac_ringEquiv {A B K L : Type} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    (e : A ≃+* B) (φ : K →+* L) (h : ∀ a, φ (algebraMap A K a) = algebraMap B L (e a)) (f : K) :
    Ring.ordFrac B (φ f) = Ring.ordFrac A f := by
  have key : ∀ a : A, Ring.ordFrac B (algebraMap B L (e a)) = Ring.ordFrac A (algebraMap A K a) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp
    have hea : e a ≠ 0 := by simpa using ha
    rw [Ring.ordFrac_eq_ord (R := B) (K := L), Ring.ordFrac_eq_ord (R := A) (K := K)]
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, ha, hea, not_false_eq_true, ite_true,
      ord_ringEquiv]
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) f
  dsimp only at hxy
  subst hxy
  have hspec := IsLocalization.mk'_spec K x y
  have h1 : Ring.ordFrac A (IsLocalization.mk' K x y) * Ring.ordFrac A (algebraMap A K y) =
      Ring.ordFrac A (algebraMap A K x) := by rw [← map_mul, hspec]
  have h2 : Ring.ordFrac B (φ (IsLocalization.mk' K x y)) * Ring.ordFrac B (algebraMap B L (e y)) =
      Ring.ordFrac B (algebraMap B L (e x)) := by rw [← map_mul, ← h, ← map_mul, hspec, h]
  rw [key, key] at h2
  have hy : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have hc : Ring.ordFrac A (algebraMap A K y) ≠ 0 := (map_ne_zero _).mpr hy
  exact mul_right_cancel₀ hc (h2.trans h1.symm)

private theorem isIso_stalkMap_restrict_of_isIso {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (x : s ⁻¹ᵁ U) : IsIso ((s ∣_ U).stalkMap x) := by
  have h : IsOpenImmersion (s ∣_ U) := inferInstance
  exact LocallyRingedSpace.IsOpenImmersion.stalk_iso (H := h) (s ∣_ U).toLRSHom x

theorem isIso_stalkMap_of_isIso_restrict {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (w : Y) (hw : s w ∈ U) : IsIso (s.stalkMap w) := by
  have hw' : w ∈ s ⁻¹ᵁ U := hw
  have e := morphismRestrictStalkMap s U ⟨w, hw'⟩
  have hi : IsIso ((s ∣_ U).stalkMap ⟨w, hw'⟩) := isIso_stalkMap_restrict_of_isIso s U _
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).mp hi

theorem coheight_eq_of_isIso_stalkMap {X Y : Scheme.{0}} (s : Y ⟶ X) (w : Y)
    [IsIso (s.stalkMap w)] : Order.coheight w = Order.coheight (s w) := by
  apply WithBot.coe_injective
  rw [← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  exact (ringKrullDim_eq_of_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv).symm

theorem ord_functionFieldMap_of_isIso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (w : Y)
    [IsIso (s.stalkMap w)] (f : X.functionField) :
    Scheme.ord (functionFieldMap s f) w = Scheme.ord f (s w) := by
  have hco := coheight_eq_of_isIso_stalkMap s w
  by_cases hc : Order.coheight (s w) = 1
  · have hw : Order.coheight w = 1 := hco.trans hc
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hw, Scheme.ord_eq_ordHom_of_coheight_eq_one hc]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (s w)) := krullDimLE_of_coheight_le hc.le
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
    congr 2
    exact ordFrac_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv (functionFieldMap s)
      (fun a => functionFieldMap_algebraMap s w a) f
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hc,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hc (hco ▸ h))]

theorem coheight_eq_and_mult_pullCart : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (U : X.Opens), IsIso (s ∣_ U) → ∀ w : Y, s w ∈ U → Order.coheight w = Order.coheight (s w) ∧ ∀ D : CartierDiv X, (pullCart s D).mult w = D.mult (s w) := by
  intro X Y _ _ s _ _ _ U hU w hw
  haveI := hU
  haveI := isIso_stalkMap_of_isIso_restrict s U w hw
  refine ⟨coheight_eq_of_isIso_stalkMap s w, fun D => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn (s w)
  rw [(isEqn_pullCart s hg).mult_eq, hg.mult_eq]
  exact ord_functionFieldMap_of_isIso s w (g : X.functionField)

end GlobalTheory.Discrepancy.MultIso
