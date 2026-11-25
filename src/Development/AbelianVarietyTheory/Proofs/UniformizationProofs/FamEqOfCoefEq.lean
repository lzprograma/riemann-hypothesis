module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefDet

theorem fn_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType p] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Spec (CommRingCat.of F) ⟶ Y, r ≫ p = 𝟙 _ → ∀ z, r z ∈ U → gs r z U a = gs r z U b) : a = b := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn (Y.basicOpen (a - b)).isOpen.isLocallyClosed
  let r := pointOfClosedPoint p c hc
  let z : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  have hz : r z ∈ Y.basicOpen (a - b) := (congrArg (· ∈ Y.basicOpen (a - b)) (pointOfClosedPoint_apply p c hc z)).mpr hcW
  have hU : r z ∈ U := Y.basicOpen_le _ hz
  have e := h r (pointOfClosedPoint_comp p c hc) z hU
  have hu : IsUnit (gs r z U (a - b)) := by
    rw [gs_eq r z U hU, ← Scheme.mem_basicOpen _ _ z hU, ← Scheme.preimage_basicOpen]
    exact hz
  rw [gs_eq r z U hU, gs_eq r z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [gs_eq r z U hU, e] at hu
  exact not_isUnit_zero hu

theorem fam_eq_of_coef_eq : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (s s' : Fam D.toPre F k), (∀ g : GtPtF D.toPre F, ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ ∀ χ, coef s g w χ = coef s' g w χ) → s = s' := by
  intro hL R _ _ _ I hA D F _ _ _ k s s' H
  have hsm := D.toPre.P.isAb.smooth
  let p : (DegPre.BF D.toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.toPre.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.toPre.P.A.hom))
  have : IsReduced (DegPre.BF D.toPre F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine fam_ext fun χ j => fn_ext_of_points p fun r hr z hz => ?_
  let r' : TF (R := R) F ⟶ DegPre.BF D.toPre F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.toPre.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL R I hA D F).1 (r' ≫ snd _ _)
  have er : lift (𝟙 (TF (R := R) F)) g.b = r' := by
    rw [hg]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  obtain ⟨w, hw, hc⟩ := H g
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.toPre.P.isLB z
  have a := CoefBasic.isCoef_coef g hw χ s z J hJ
  have a' := CoefBasic.isCoef_coef g hw χ s' z J hJ
  rw [hc χ, a', Units.mul_left_inj, Units.mul_left_inj, er] at a
  exact (sec_trans (s.s χ) r z hz (hJ.mem _ r)).trans ((congrArg _ a.symm).trans
    (sec_trans (s'.s χ) r z hz (hJ.mem _ r)).symm)

end GlobalTheory.UT.CoefDet
end
