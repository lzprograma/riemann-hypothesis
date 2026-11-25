module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.Square

section General
variable {X Y : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

private theorem map_zpow_zpow {M N : Type} [Group M] [Group N] (F : M →* N) (x : M) (n e : ℤ) :
    F (x ^ n) ^ e = F x ^ (n * e) := by
  rw [map_zpow, ← zpow_mul]

theorem linComb_pw (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (n : ℤ) :
    LB.LinComb (pw L n) φ ε = LB.LinComb L φ (fun k => n * ε k) := by
  unfold LB.LinComb GlobalTheory.AbLaw.pw
  congr 1
  funext j j'
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact map_zpow_zpow _ _ _ _

private theorem sameSum_of_prod_pow_eq' {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U), ∏ k, f (φ₁ k) ^ ε₁ k = ∏ k, f (φ₂ k) ^ ε₂ k) :
    LB.SameSum φ₁ ε₁ φ₂ ε₂ := by
  classical
  intro ψ
  have e := congrArg Multiplicative.toAdd
    (h (Multiplicative ℤ) (fun χ => Multiplicative.ofAdd (if χ = ψ then (1 : ℤ) else 0)))
  simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_ite, mul_zero] at e
  convert e <;> simp

theorem triv_mul (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (h₁ : Triv (LB.LinComb L φ ε)) (h₂ : Triv (LB.LinComb L φ' ε'))
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (φ k) ^ ε k) * ∏ k, f (φ' k) ^ ε' k = ∏ k, f (φ'' k) ^ ε'' k) : Triv (LB.LinComb L φ'' ε'') := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  have hs : LB.SameSum (Sum.elim φ φ') (Sum.elim ε ε') φ'' ε'' := sameSum_of_prod_pow_eq' fun U _ f => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact h U f
  obtain ⟨t, ht, -⟩ := DVR.gen_transport hL hs (LB.mulGen L φ ε φ' ε' t₁ t₂)
    (DVR.mulGen_isGen L φ ε φ' ε' t₁ t₂ ht₁ ht₂)
  exact ⟨t, ht⟩

theorem triv_inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Triv (LB.LinComb L φ ε)) :
    Triv (LB.LinComb L φ fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B}
  {A : Type} [CommRing A] [IsLocalRing A] {t : Spec (CommRingCat.of A) ⟶ S}


omit [IsCommMonObj B] in
theorem triv_const {K : Type} [Fintype K] (x : K → (Over.mk t ⟶ B)) (ε : K → ℤ) :
    Triv (LB.LinComb L.L (fun k => (fst (Over.mk t) B ≫ x k).left) ε) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := A) L.L L.isLB (fun k => (x k).left) ε
  exact ⟨LB.pullGen L.L (fun k => (x k).left) ε e (fst (Over.mk t) B).left,
    DVR.pullGen_isGen L.L _ ε e he _⟩

private theorem translPt_eq_fst_comp_mul_snd {T : Over S} (w : T ⟶ B) : translPt B w = (fst T B ≫ w) * snd T B := by
  unfold translPt
  rw [Hom.mul_def]

theorem triv_square (c : CubicalStr B L) (x y : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left,
      (translPt B y).left] ![1, 1, -1, -1]) := by
  have h₁ : Triv (LB.LinComb L.L (fun k => (lift (fst (Over.mk t) B ≫ x)
      (lift (fst (Over.mk t) B ≫ y) (snd (Over.mk t) B))).left ≫ thφ B (x3 B) k) thε) :=
    ⟨LB.pullGen L.L (thφ B (x3 B)) thε c.t _, DVR.pullGen_isGen L.L _ _ c.t c.isGen _⟩
  have h₂ := triv_const (L := L) (t := t) (K := Fin 4) ![x * y, x, y, 1] ![1, -1, -1, 1]
  refine triv_mul L.isLB h₁ h₂ fun U _ f => ?_
  rw [Geo.Tor.prod_cub]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    zpow_one, zpow_neg]
  simp only [translPt_eq_fst_comp_mul_snd, MonObj.comp_mul, MonObj.comp_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem triv_pow (c : CubicalStr B L) (r : ℕ) (x : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 3) ![(translPt B (x ^ r)).left, (translPt B x).left, (snd (Over.mk t) B).left]
      ![1, -r, r - 1]) := by
  induction r with
  | zero =>
    have h₀ := triv_const (L := L) (t := t) (K := Fin 0) ![] ![]
    refine triv_mul L.isLB h₀ h₀ fun U _ f => ?_
    rw [pow_zero, translPt_eq_fst_comp_mul_snd, MonObj.comp_one, _root_.one_mul]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    push_cast
    module
  | succ r ih =>
    have hs := triv_square c (x ^ r) x
    refine triv_mul L.isLB hs ih fun U _ f => ?_
    rw [pow_succ]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    push_cast
    module

theorem square_of_cubical : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (L : RigLB B) (_ : CubicalStr B L) (A : Type) [CommRing A] [IsLocalRing A] (t : Spec (CommRingCat.of A) ⟶ S), (∀ x y : Over.mk t ⟶ B, Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left, (translPt B y).left] ![1, 1, -1, -1])) ∧ ∀ (r : ℕ) (x : Over.mk t ⟶ B), Triv (translDiff B (pw L.L r) x) ↔ Triv (translDiff B L.L (x ^ r)) := by
  intro S B _ _ L c A _ _ t
  refine ⟨fun x y => triv_square c x y, fun r x => ?_⟩
  have hP := triv_pow c r x
  unfold translDiff
  rw [linComb_pw]
  simp only [← Hom.mul_def]
  simp only [translPt_eq_fst_comp_mul_snd] at hP
  constructor
  · intro h
    refine triv_mul L.isLB h hP fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · intro h
    refine triv_mul L.isLB h (triv_inv hP) fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module

end GlobalTheory.Square
end
