module

import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.SecRatio

private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

private theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (e : U ≤ V) (a : R) : resG X e (constFn p V a) = constFn p U a := by
  unfold constFn
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  erw [Scheme.Hom.appLE_map]

variable {X : Scheme.{0}} {H : LB X}

theorem compat_res (s : H.Sec) (i j : H.ι) {V : X.Opens} (hi : V ≤ H.U i) (hj : V ≤ H.U j) :
    resG X hi (s.f i) = resG X (le_inf hi hj) (H.g i j : Γ(X, H.U i ⊓ H.U j)) * resG X hj (s.f j) := by
  exact GlobalTheory.Cartier.sec_compat s i j hi hj

theorem isUnit_res (t : H.Sec) (l : H.ι) {V : X.Opens} (hV : V ≤ Out.nonzeroLocus t)
    (hl : V ≤ H.U l) : IsUnit (resG X hl (t.f l)) := by
  apply GlobalTheory.ProjSpace.isUnit_resG_sec <;> assumption

theorem existsUnique_isRatio (hH : H.IsLB) (s t : H.Sec) (W : X.Opens)
    (hW : W ≤ Out.nonzeroLocus t) : ∃! r : Γ(X, W), IsRatio s t W r := by
  have hu : ∀ l, IsUnit (resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l)) :=
    fun l => isUnit_res t l (inf_le_left.trans hW) _
  have hq : ∀ l, ∃ q : Γ(X, W ⊓ H.U l), resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) =
      q * resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l) := fun l =>
    ⟨resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) * ↑(hu l).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : W ≤ ⨆ l, W ⊓ H.U l := by
    rw [← inf_iSup_eq, hH.cover, inf_top_eq]
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun l => W ⊓ H.U l) q := by
    intro i j
    change resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i) (q i) =
      resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j) (q j)
    have hi : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U i := inf_le_left.trans inf_le_right
    have hj : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U j := inf_le_right.trans inf_le_right
    have e1 := congrArg (resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have u := isUnit_res t i ((inf_le_left.trans inf_le_left).trans hW) hi
    apply u.mul_right_cancel
    rw [← e1, compat_res s i j hi hj, compat_res t i j hi hj, e2]
    ring
  obtain ⟨r, hr, hr'⟩ := X.sheaf.existsUnique_gluing' (fun l => W ⊓ H.U l) W
    (fun l => homOfLE inf_le_left) hcov q hcomp
  refine ⟨r, fun l => ?_, fun r' h' => hr' r' fun l => ?_⟩
  · have : resG X (inf_le_left : W ⊓ H.U l ≤ W) r = q l := hr l
    rw [this]; exact hq l
  · change resG X (inf_le_left : W ⊓ H.U l ≤ W) r' = q l
    apply (hu l).mul_right_cancel
    rw [← hq l]; exact (h' l).symm

theorem existsUnique_isLin {k : Type} [CommRing k] (p : X ⟶ Sp k) {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → k) : ∃! φ : H.Sec, IsLin p s a φ := by
  refine ⟨⟨fun l => ∑ j, constFn p (H.U l) (a j) * (s j).f l, fun i j => ?_⟩, fun l => rfl, ?_⟩
  · change resG X inf_le_left _ = _ * resG X inf_le_right _

    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_mul, res_const, res_const]
    have : resG X inf_le_left _ = _ * resG X inf_le_right _ := (s n).compat i j
    rw [this]; ring
  · rintro ⟨f, hf⟩ h
    have : f = _ := funext h
    subst this
    rfl

theorem ratio_and_lin : (∀ (X : Scheme.{0}) (H : LB X), H.IsLB → (∀ (s t : H.Sec) (W : X.Opens), W ≤ Out.nonzeroLocus t → ∃! r : Γ(X, W), IsRatio s t W r) ∧ ∀ (k : Type) [CommRing k] (p : X ⟶ Sp k) (J : Type) [Fintype J] (s : J → H.Sec) (a : J → k), ∃! φ : H.Sec, IsLin p s a φ) :=
  fun _ _ hH => ⟨existsUnique_isRatio hH, fun _ _ p _ _ s a => existsUnique_isLin p s a⟩

end GlobalTheory.SecRatio
