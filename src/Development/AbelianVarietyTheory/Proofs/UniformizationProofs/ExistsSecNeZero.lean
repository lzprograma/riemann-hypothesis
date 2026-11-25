module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.NonVan
open GlobalTheory.UT.CoefBasic

theorem val_powFrame {S : Scheme.{0}} {A : Over S} (L : LB A.left) {T : Over S} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame A L x τ k) r z J = val τ r z J ^ k :=
  map_zpow _ _ _

theorem exists_sec_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 4 ≤ k → ∀ (x : TFK (R := R) F ⟶ A.A) (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), e.IsGen → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) := by
  intro hL R _ _ A F _ _ k hk x e he
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  obtain ⟨t, ht⟩ := GlobalTheory.TwistUnit.unitAt_pow hL.1.ample A k hk (snd (TFK (R := R) F) A.A).left
    ((ptSecT A.A x).left z)
  have hu := GlobalTheory.TwistUnit.isUnit_sval_of A.isLB t (ptSecT A.A x).left z ht J' hJ'
  obtain ⟨c, hc⟩ := cstH_surj z (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val
  refine ⟨t, c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq (R := R) z z'
    have a₁ := sval_tr t (ptSecT A.A x).left hJ hJ'
    have a₂ := val_tr he (𝟙 _) hJ hJ'
    have hx : (ptSecT A.A x).left ≫ (snd (TFK (R := R) F) A.A).left = x.left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [Fin.prod_univ_one, hx, ← hu.unit_spec] at a₁
    rw [Fin.prod_univ_one, Category.id_comp, zpow_one] at a₂
    have a₃ : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) =
        (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val := (cst_eq z c).trans hc
    refine a₁.trans ?_
    rw [a₃, val_powFrame, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module

end GlobalTheory.UT.NonVan
end
