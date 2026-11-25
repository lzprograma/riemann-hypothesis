module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GoodPtOfIrredOfMulPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TorsionDense

open GoodPoint

theorem exists_sec_lPow {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (T : Over S) (k : ℕ)
    (s : (lbPow L k).Sec) : ∃ s' : LB.Sec (LPow A L k T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → (IsUnit (powVal s' r z J) ↔ (r ≫ (snd T A).left) z ∈ nonzeroLocus s) := by
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (k : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, -Over.snd_left])
    (pullMulSec (L := L) (φ := fun _ : PUnit => 𝟙 A.left) (ε := fun _ => (k : ℤ)) s (snd T A).left
      (LB.oneGen L (Y := (T ⊗ A).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm))
  refine ⟨s', fun Z r z J hJ => ?_⟩
  have e := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ _ r z hJ)
  refine (iff_of_eq (congrArg IsUnit e)).trans ?_
  rw [Units.isUnit_mul_units]
  exact (mem_nonzeroLocus_iff_pull s _ z (hJ.mem (fun _ : PUnit => 𝟙 A.left) _)).symm

variable {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K)))

theorem exists_mem_nonzeroLocus (hI : IrredSt) (hK : KerPowSt) (k : ℕ) (hk : 4 ≤ k) (hkK : (k : K) ≠ 0)
    (B : Set (baseOver (Spec (CommRingCat.of K)) ⟶ P.A)) (hB : ∀ w, w ^ k = 1 → ∀ b ∈ B, w * b ∈ B)
    (s t : (lbPow P.L k).Sec) (x : P.A.left) (hx : x ∈ nonzeroLocus s)
    (b : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (hb : b ∈ B)
    (p : (baseOver (Spec (CommRingCat.of K))).left) (ht : b.left p ∈ nonzeroLocus t) :
    ∃ b' ∈ B, ∃ p', b'.left p' ∈ nonzeroLocus s := by
  by_contra hcon
  obtain ⟨s', hs'⟩ := exists_sec_lPow P.isLB (baseOver _) k s
  obtain ⟨t', ht'⟩ := exists_sec_lPow P.isLB (baseOver _) k t
  rcases hI K P k (Or.inr hk) hkK (vanishing P.L _ B)
    (fun θ s s' h hsB q hq y J hJ => by
      obtain ⟨c, hc⟩ := powVal_act h (ptSecT P.A q).left hJ
      rw [← Over.comp_left, ptSecT_translT] at hc
      refine (congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr
        (Ideal.mul_mem_left _ _ (hsB _ (hB _ ?_ q hq) y J hJ))
      exact (hK _ P k (by omega) _ θ.pt).1 fun p => ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩) with h | h
  · have hm : SecM.ofSec P.A s' ∈ vanishing P.L _ B := fun q hq y J hJ hu => by
      have := (hs' _ _ y J hJ).1 hu
      rw [← Over.comp_left, ptSecT_snd] at this
      exact hcon ⟨q, hq, y, this⟩
    rw [h, Submodule.mem_bot] at hm
    choose J hJ using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ x)
    have hu := (hs' _ (unitInv P.A).left x J hJ).2 (by rw [← Over.comp_left, unitInv_snd]; exact hx)
    have e : powVal s' (unitInv P.A).left x J = 0 :=
      (congrArg (gs _ x _) (congrFun (congrArg Subtype.val hm) _)).trans (gs_zero _ x _)
    rw [e] at hu
    exact not_isUnit_zero hu
  · choose J hJ using fun χ : (baseOver (Spec (CommRingCat.of K))).left ⟶ P.A.left => exists_chart P.isLB (χ p)
    have hm : SecM.ofSec P.A t' ∈ vanishing P.L _ B := by rw [h]; trivial
    exact hm b hb p J hJ ((ht' _ _ p J hJ).2 (by rw [← Over.comp_left, ptSecT_snd]; exact ht))

theorem dense_torsion [CharZero K] (hI : IrredSt) (hK : KerPowSt) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}, Set.range x.left) := by
  have := P.isAb.comm
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨n, hn, s, hs, hle, -⟩ := hA.exists_affine_le (x := x) (U := ⟨U, hU⟩) hx
  let p : (baseOver (Spec (CommRingCat.of K))).left := IsLocalRing.closedPoint K
  obtain ⟨m, hm, t, ht, -⟩ := hA.exists_affine ((1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p)
  have e₁ := nonzeroLocus_secPow s (k := m * 4) (by omega)
  have e₂ := nonzeroLocus_secPow t (k := n * 4) (by omega)
  have hk : 4 ≤ n * (m * 4) := by nlinarith [Nat.mul_pos hn hm]
  obtain ⟨b, hb, q, hq⟩ := exists_mem_nonzeroLocus P hI hK (n * (m * 4)) hk (Nat.cast_ne_zero.2 (by omega))
    {x | ∃ n : ℕ, 0 < n ∧ x ^ n = 1} (fun w hw b ⟨l, hl, hb⟩ => ⟨n * (m * 4) * l, Nat.mul_pos (by omega) hl, by
      rw [mul_pow, pow_mul w, hw, one_pow, mul_comm _ l, pow_mul, hb, one_pow, _root_.one_mul]⟩)
    (secPow s (m * 4)) (secCast (by ring) (secPow t (n * 4))) x (e₁.ge hs) 1 ⟨1, one_pos, one_pow _⟩ p (e₂.ge ht)
  exact ⟨b.left q, hle (e₁.le hq), Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

end GlobalTheory.TorsionDense
