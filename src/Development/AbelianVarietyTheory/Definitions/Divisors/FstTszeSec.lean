module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

open CategoryTheory GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}


open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_nil {O : Type} [CommRing O] [Algebra ℂ O] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ O (Fin g → O)).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]


variable (K) in
@[reducible] def jet (k : K.K) : K.Obj where
  k := k
  C := TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))
  alg := ((TrivSqZeroExt.inlHom _ _).comp (K.cst k)).toAlgebra
  J := RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (K.W k)) (Fin g → Hol (K.W k))).toRingHom
  nil := tsze_nil
  ρ := TrivSqZeroExt.inlHom _ _
  ρ_cst _ := rfl

def tszeSec {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) : O →+* TrivSqZeroExt O (Fin g → O) where
  toFun h := TrivSqZeroExt.inl h + TrivSqZeroExt.inr fun a ↦ D a h
  map_one' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_zero' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)


open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.fst_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).fst = h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]


open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.snd_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) (a : Fin g) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).snd a = D a h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]

def jetSec (k : K.K) : Hol (K.W k) →+* TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) := tszeSec dw


open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_expand {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + TrivSqZeroExt.inr v : TrivSqZeroExt O (Fin g → O)) = TrivSqZeroExt.inl h +
      ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) := by
  congr 1
  simp only [TrivSqZeroExt.inl_mul_inr]
  ext b
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

def jet0 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  ptHom (K.jet k) (K.le_refl k)

def jet1 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  fromTriv (K.jet k) (K.le_refl k) (jetSec k)
    (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, sh_refl]
        exact tsze_expand h fun a ↦ dw a h⟩)

end GlobalTheory.AnPer.Charts
