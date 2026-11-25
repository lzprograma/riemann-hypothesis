module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.DescNorm

open GlobalTheory.LBDescent

section General

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def twist (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (u : Γ(pullback f f, ⊤)ˣ) :
    ∀ i j, Γ(pullback f f, chart f L i j)ˣ :=
  fun i j => φ i j * res le_top u

def Defect (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (r : T ⟶ Triple f) (t : T) (i j k : L.ι),
    pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (r t)) ∈ L.U i →
    pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (r t)) ∈ L.U j →
    pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (r t)) ∈ L.U k →
    gm r t ⊤ D * gm (r ≫ pr13 f) t _ (φ i k) =
      gm (r ≫ pullback.fst (pullback.snd f f) (pullback.fst f f)) t _ (φ i j) *
        gm (r ≫ pullback.snd (pullback.snd f f) (pullback.fst f f)) t _ (φ j k)

end General

section Product

variable {S : Scheme.{0}} {A A' B : Over S} [GrpObj B]


variable (A B) in
def zb : A ⊗ B ⟶ A ⊗ B := lift (fst A B) (1 : A ⊗ B ⟶ B)

theorem zb_whiskerRight (q : A ⟶ A') : zb A B ≫ q ▷ B = q ▷ B ≫ zb A' B := by
  ext <;> simp [zb]

theorem zb_left_whiskerRight (q : A ⟶ A') :
    (q ▷ B).left ≫ (zb A' B).left = (zb A B).left ≫ (q ▷ B).left := by
  rw [← Over.comp_left, ← Over.comp_left, zb_whiskerRight]

def rhoZ (q : A ⟶ A') : pullback (q ▷ B).left (q ▷ B).left ⟶ pullback (q ▷ B).left (q ▷ B).left :=
  pullback.map (q ▷ B).left (q ▷ B).left (q ▷ B).left (q ▷ B).left (zb A B).left (zb A B).left (zb A' B).left
    (zb_left_whiskerRight q) (zb_left_whiskerRight q)

@[reassoc (attr := simp)]
theorem rhoZ_fst (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.fst (q ▷ B).left (q ▷ B).left =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (zb A B).left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rhoZ_snd (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.snd (q ▷ B).left (q ▷ B).left =
    pullback.snd (q ▷ B).left (q ▷ B).left ≫ (zb A B).left :=
  pullback.lift_snd _ _ _

def rhoW (q : A ⟶ A') : Triple (q ▷ B).left ⟶ Triple (q ▷ B).left :=
  pullback.map (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left)
    (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) (rhoZ q) (rhoZ q) (zb A B).left
    (rhoZ_snd q).symm (rhoZ_fst q).symm

@[reassoc (attr := simp)]
theorem rhoW_fst (q : A ⟶ A') :
    rhoW (B := B) q ≫ pullback.fst (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) =
      pullback.fst (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) ≫ rhoZ q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rhoW_snd (q : A ⟶ A') :
    rhoW (B := B) q ≫ pullback.snd (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) =
      pullback.snd (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) ≫ rhoZ q :=
  pullback.lift_snd _ _ _

variable [GrpObj A]

def NormAlong (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B)))
    (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (r : T ⟶ pullback (q ▷ B).left (q ▷ B).left) (t : T) (i j : P.ι),
    pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q (r t)) ∈ P.U i →
    pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q (r t)) ∈ P.U j →
    gm (r ≫ rhoZ q) t _ (φ i j) =
      (gm (r ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) t _ (τ.s fun _ => i))⁻¹ *
        gm (r ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) t _ (τ.s fun _ => j)

end Product

end GlobalTheory.DescNorm
