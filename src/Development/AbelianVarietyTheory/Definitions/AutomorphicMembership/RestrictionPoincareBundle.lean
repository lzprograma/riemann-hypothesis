module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial, Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.Vert

namespace GlobalTheory.FormalPic

section Iso

variable {X Y : Scheme.{0}} {A B C : LB X}

theorem isGen_iso_iff (u : LB.Iso A B) : u.IsGen ↔ ∀ (x : X) (p q : B.ι × A.ι), x ∈ B.U p.1 ⊓ A.U p.2 → x ∈ B.U q.1 ⊓ A.U q.2 →
    gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2) (u.s p) =
      gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x (B.U q.1 ⊓ A.U q.2) (u.s q) := by
  refine (isGen_iff_germ u).trans (forall₃_congr fun x p q => forall₂_congr fun hp hq => ?_)
  rw [gm_div' B A (𝟙 X) x p q hp hq]
  rfl

theorem gm_congr {U V : X.Opens} {a : Γ(X, U)ˣ} {b : Γ(X, V)ˣ} {W : X.Opens} {c : Γ(X, W)ˣ}
    (h : ∀ x ∈ U ⊓ V ⊓ W, gm (𝟙 X) x U a = gm (𝟙 X) x V b * gm (𝟙 X) x W c) (f : Y ⟶ X) (y : Y)
    (hy : f y ∈ U ⊓ V ⊓ W) : gm f y U a = gm f y V b * gm f y W c := by
  have e : res (inf_le_left.trans inf_le_left : U ⊓ V ⊓ W ≤ U) a =
      res (inf_le_left.trans inf_le_right : U ⊓ V ⊓ W ≤ V) b * res (inf_le_right : U ⊓ V ⊓ W ≤ W) c :=
    unit_ext fun x hx => by rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]; exact h x hx
  have := congrArg (gm f y _) e
  rwa [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy] at this

theorem exists_trans (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) {u : LB.Iso A B} {v : LB.Iso B C} (hu : u.IsGen)
    (hv : v.IsGen) : ∃ w : LB.Iso A C, w.IsGen ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (a : A.ι) (b : B.ι) (c : C.ι),
      f y ∈ A.U a → f y ∈ B.U b → f y ∈ C.U c → gm f y (C.U c ⊓ A.U a) (w.s (c, a)) =
        gm f y (C.U c ⊓ B.U b) (v.s (c, b)) * gm f y (B.U b ⊓ A.U a) (u.s (b, a)) := by
  rw [isGen_iso_iff] at hu hv
  have glue : ∀ (c : C.ι) (a : A.ι), ∃ s : Γ(X, C.U c ⊓ A.U a)ˣ, ∀ (x : X) (b : B.ι), x ∈ A.U a → x ∈ B.U b → x ∈ C.U c →
      gm (𝟙 X) x _ s = gm (𝟙 X) x (C.U c ⊓ B.U b) (v.s (c, b)) * gm (𝟙 X) x (B.U b ⊓ A.U a) (u.s (b, a)) := by
    intro c a
    have l₁ : ∀ b, C.U c ⊓ A.U a ⊓ B.U b ≤ C.U c ⊓ B.U b := fun b x hx => ⟨hx.1.1, hx.2⟩
    have l₂ : ∀ b, C.U c ⊓ A.U a ⊓ B.U b ≤ B.U b ⊓ A.U a := fun b x hx => ⟨hx.2, hx.1.2⟩
    have val : ∀ b, ∀ x ∈ C.U c ⊓ A.U a ⊓ B.U b, gm (𝟙 X) x _ (res (l₁ b) (v.s (c, b)) * res (l₂ b) (u.s (b, a))) =
        gm (𝟙 X) x (C.U c ⊓ B.U b) (v.s (c, b)) * gm (𝟙 X) x (B.U b ⊓ A.U a) (u.s (b, a)) := fun b x hx =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _) (gm_res _ x _ hx _))
    obtain ⟨s, hs⟩ := glue_unit (C.U c ⊓ A.U a) (fun b => C.U c ⊓ A.U a ⊓ B.U b) (fun _ => inf_le_left)
      (fun x hx => by
        obtain ⟨b, hb⟩ := exists_chart hB x
        exact Opens.mem_iSup.2 ⟨b, hx, hb⟩)
      (fun b => res (l₁ b) (v.s (c, b)) * res (l₂ b) (u.s (b, a))) (fun b b' x hx => by
        rw [val b x hx.1, val b' x hx.2, hu x (b, a) (b', a) (l₂ b hx.1) (l₂ b' hx.2),
          hv x (c, b) (c, b') (l₁ b hx.1) (l₁ b' hx.2), gm_self hA (𝟙 X) x hx.1.1.2, gm_self hC (𝟙 X) x hx.1.1.1,
          inv_one, mul_one, one_mul, mul_mul_mul_comm, inv_mul_cancel, one_mul])
    refine ⟨s, fun x b ha hb hc => ?_⟩
    have hx : x ∈ C.U c ⊓ A.U a ⊓ B.U b := ⟨⟨hc, ha⟩, hb⟩
    exact (gm_res (𝟙 X) x inf_le_left hx s).symm.trans ((congrArg (gm (𝟙 X) x _) (hs b)).trans (val b x hx))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, (isGen_iso_iff _).2 fun x p q hp hq => ?_, fun Y f y a b c ha hb hc =>
    gm_congr (fun x hx => hs c a x b hx.1.1.2 hx.2.1 hx.1.1.1) f y ⟨⟨⟨hc, ha⟩, hc, hb⟩, hb, ha⟩⟩
  obtain ⟨b, hb⟩ := exists_chart hB x
  refine (hs p.1 p.2 x b hp.2 hb hp.1).trans (Eq.trans ?_ (congrArg _ (hs q.1 q.2 x b hq.2 hb hq.1).symm))
  rw [hu x (b, p.2) (b, q.2) ⟨hb, hp.2⟩ ⟨hb, hq.2⟩, hv x (p.1, b) (q.1, b) ⟨hp.1, hb⟩ ⟨hq.1, hb⟩,
    gm_self hB (𝟙 X) x hb, inv_one, mul_one, one_mul, mul_mul_mul_comm]

end Iso

variable {X : ℕ → Scheme.{0}} (i : ∀ e, X e ⟶ X (e + 1))

structure FLB : Type 1 where

  ι : Type

  U : ∀ e, ι → (X e).Opens

  g : ∀ e a b, Γ(X e, U e a ⊓ U e b)ˣ
  isLB : ∀ e, LB.IsLB ⟨ι, U e, g e⟩
  U_eq : ∀ e a, U e a = i e ⁻¹ᵁ U (e + 1) a
  g_eq : ∀ e a b, g e a b = res (U := i e ⁻¹ᵁ (U (e + 1) a ⊓ U (e + 1) b))
    (le_inf (inf_le_left.trans (U_eq e a).le) (inf_le_right.trans (U_eq e b).le)) (pullU (i e) _ (g (e + 1) a b))

variable {i}

theorem eq_res_pullU_iff {Y Z : Scheme.{0}} (f : Z ⟶ Y) {U : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : Γ(Z, V)ˣ)
    (b : Γ(Y, U)ˣ) : a = res h (pullU f U b) ↔ ∀ z ∈ V, gm (𝟙 Z) z V a = gm f z U b := by
  have e : ∀ z ∈ V, gm (𝟙 Z) z V (res h (pullU f U b)) = gm f z U b := fun z hz =>
    (gm_res _ z h hz _).trans ((gm_pull (𝟙 Z) f z U (h hz) b).trans (by rw [Category.id_comp]))
  exact ⟨fun H z hz => H ▸ e z hz, fun H => unit_ext fun z hz => (H z hz).trans (e z hz).symm⟩

namespace FLB

abbrev lb (L : FLB i) (e : ℕ) : LB (X e) := ⟨L.ι, L.U e, L.g e⟩

theorem mem_succ (L : FLB i) {e : ℕ} {a : L.ι} {x : X e} (h : x ∈ L.U e a) : i e x ∈ L.U (e + 1) a := (L.U_eq e a).le h

def Compat {L M : FLB i} (u : ∀ e, LB.Iso (L.lb e) (M.lb e)) : Prop :=
  ∀ e (p : M.ι × L.ι), (u e).s p = res (U := i e ⁻¹ᵁ (M.U (e + 1) p.1 ⊓ L.U (e + 1) p.2))
    (le_inf (inf_le_left.trans (M.U_eq e p.1).le) (inf_le_right.trans (L.U_eq e p.2).le)) (pullU (i e) _ ((u (e + 1)).s p))

theorem compat_iff {L M : FLB i} (u : ∀ e, LB.Iso (L.lb e) (M.lb e)) : Compat u ↔ ∀ e (p : M.ι × L.ι), ∀ x ∈ M.U e p.1 ⊓ L.U e p.2,
    gm (𝟙 _) x (M.U e p.1 ⊓ L.U e p.2) ((u e).s p) = gm (i e) x (M.U (e + 1) p.1 ⊓ L.U (e + 1) p.2) ((u (e + 1)).s p) :=
  forall₂_congr fun _ _ => eq_res_pullU_iff _ _ _ _

def Iso (L M : FLB i) : Prop := ∃ u : ∀ e, LB.Iso (L.lb e) (M.lb e), (∀ e, (u e).IsGen) ∧ Compat u

def reindex (L : FLB i) {κ : Type} (j : κ → L.ι) (h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k)) : FLB i where
  ι := κ
  U e k := L.U e (j k)
  g e k l := L.g e (j k) (j l)
  isLB e := ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 (h e x), fun _ => (L.isLB e).g_self _,
    fun _ _ _ => (L.isLB e).cocycle _ _ _⟩
  U_eq e k := L.U_eq e (j k)
  g_eq e k l := L.g_eq e (j k) (j l)

theorem reindex_iso (L : FLB i) {κ : Type} (j : κ → L.ι) (h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k)) :
    (L.reindex j h).Iso L := by
  refine ⟨fun e => ⟨fun p => L.g e p.1 (j p.2)⟩, fun e => (isGen_iso_iff _).2 fun x p q hp hq => ?_,
    fun e p => L.g_eq e p.1 (j p.2)⟩
  have a := gm_cocycle (L.isLB e) (𝟙 _) x hp.1 hq.1 hq.2
  have b := gm_cocycle (L.isLB e) (𝟙 _) x hp.1 hp.2 hq.2
  exact (eq_mul_inv_of_mul_eq (b.trans a.symm)).trans (mul_right_comm _ _ _)

theorem Iso.refl (L : FLB i) : L.Iso L := L.reindex_iso id fun e => exists_chart (L.isLB e)

theorem Iso.symm {L M : FLB i} (h : L.Iso M) : M.Iso L := by
  obtain ⟨u, hu, hc⟩ := h
  have le : ∀ e (p : L.ι × M.ι), L.U e p.1 ⊓ M.U e p.2 ≤ M.U e p.2 ⊓ L.U e p.1 := fun e p y hy => ⟨hy.2, hy.1⟩
  have v : ∀ e {Z : Scheme.{0}} (f : Z ⟶ X e) (z : Z) (p : L.ι × M.ι), f z ∈ L.U e p.1 ⊓ M.U e p.2 →
      gm f z (L.U e p.1 ⊓ M.U e p.2) (res (le e p) ((u e).s (p.2, p.1)))⁻¹ =
      (gm f z (M.U e p.2 ⊓ L.U e p.1) ((u e).s (p.2, p.1)))⁻¹ := fun e Z f z p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ z _ hp _))
  refine ⟨fun e => ⟨fun p => (res (le e p) ((u e).s (p.2, p.1)))⁻¹⟩, fun e => (isGen_iso_iff _).2 fun x p q hp hq => ?_,
    (compat_iff _).2 fun e p x hx => ?_⟩
  · refine (v e _ x p hp).trans (Eq.trans ?_ (congrArg _ (v e _ x q hq).symm))
    refine (congrArg (·⁻¹) ((isGen_iso_iff _).1 (hu e) x (p.2, p.1) (q.2, q.1) (le e p hp) (le e q hq))).trans ?_
    simp only [mul_inv, inv_inv]
    exact congrArg (· * _) (mul_comm _ _)
  · exact (v e _ x p hx).trans ((congrArg (·⁻¹) ((compat_iff u).1 hc e (p.2, p.1) x (le e p hx))).trans
      (v (e + 1) _ x p ⟨L.mem_succ hx.1, M.mem_succ hx.2⟩).symm)

theorem Iso.trans {L M N : FLB i} (h : L.Iso M) (h' : M.Iso N) : L.Iso N := by
  obtain ⟨u, hu, hc⟩ := h
  obtain ⟨v, hv, hd⟩ := h'
  choose w hw hg using fun e => exists_trans (L.isLB e) (M.isLB e) (N.isLB e) (hu e) (hv e)
  refine ⟨w, hw, (compat_iff _).2 fun e p x hx => ?_⟩
  obtain ⟨b, hb⟩ := exists_chart (M.isLB e) x
  exact (hg e _ (𝟙 _) x p.2 b p.1 hx.2 hb hx.1).trans ((congrArg₂ (· * ·)
    ((compat_iff v).1 hd e (p.1, b) x ⟨hx.1, hb⟩) ((compat_iff u).1 hc e (b, p.2) x ⟨hb, hx.2⟩)).trans
    (hg (e + 1) _ (i e) x p.2 b p.1 (L.mem_succ hx.2) (M.mem_succ hb) (N.mem_succ hx.1)).symm)

instance setoid : Setoid (FLB i) := ⟨Iso, Iso.refl, Iso.symm, Iso.trans⟩

variable {Y Y' : Scheme.{0}} (q : ∀ e, X e ⟶ Y) (hq : ∀ e, i e ≫ q (e + 1) = q e)

end FLB


variable (i) in
structure FLBOn (κ : Type) : Type where

  U : ∀ e, κ → (X e).Opens

  g : ∀ e a b, Γ(X e, U e a ⊓ U e b)ˣ
  isLB : ∀ e, LB.IsLB ⟨κ, U e, g e⟩
  U_eq : ∀ e a, U e a = i e ⁻¹ᵁ U (e + 1) a
  g_eq : ∀ e a b, g e a b = res (U := i e ⁻¹ᵁ (U (e + 1) a ⊓ U (e + 1) b))
    (le_inf (inf_le_left.trans (U_eq e a).le) (inf_le_right.trans (U_eq e b).le)) (pullU (i e) _ (g (e + 1) a b))

def FLBOn.toFLB {κ : Type} (L : FLBOn i κ) : FLB i := ⟨κ, L.U, L.g, L.isLB, L.U_eq, L.g_eq⟩

def FLB.toOn (L : FLB i) : FLBOn i L.ι := ⟨L.U, L.g, L.isLB, L.U_eq, L.g_eq⟩

instance small_quotient : Small.{0} (Quotient (FLB.setoid (i := i))) := by
  refine small_of_surjective (α := FLBOn i (Σ e, X e)) (f := fun p => Quotient.mk _ p.toFLB) fun c => ?_
  obtain ⟨L, rfl⟩ := Quotient.exists_rep c
  choose j hj using fun x : Σ e, X e => exists_chart (L.isLB x.1) x.2
  have h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k) := fun e x => ⟨⟨e, x⟩, hj ⟨e, x⟩⟩
  exact ⟨(L.reindex j h).toOn, Quotient.sound (L.reindex_iso j h)⟩


variable (i) in
def FPic : Type := Shrink.{0} (Quotient (FLB.setoid (i := i)))

def level (e : ℕ) (c : FPic i) : SmallPic (X e) :=
  Quotient.lift (s := FLB.setoid) (fun L : FLB i => smallCls (L.lb e) (L.isLB e))
    (fun _ _ h => (smallCls_eq_iff _ _).2 (h.elim fun u hu => ⟨u e, hu.1 e⟩)) ((equivShrink _).symm c)

variable {Y Y' : Scheme.{0}} (q : ∀ e, X e ⟶ Y) (hq : ∀ e, i e ≫ q (e + 1) = q e)

section Projective

open GlobalTheory.ProjSpace

variable {R : Type} [CommRing R] (I : Ideal R) (N : ℕ)

end Projective

end GlobalTheory.FormalPic
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle", "h": "module\n\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (thick thickObj thickMap thickTrans)
open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf (hMap sE)
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor GlobalTheory.Vert GlobalTheory.FormalPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

section Classes

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

variable {G}




variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)

omit [IsCommMonObj G] [IsCommMonObj G'] in
def sqMap : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G'))).left

omit [IsCommMonObj G] [IsCommMonObj G'] in
@[reassoc] theorem sqMap_fst : sqMap h ≫ (fst G G).left = (fst G' G').left ≫ φ :=
  congrArg (fun q => q.left) (lift_fst (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G')))

omit [IsCommMonObj G] [IsCommMonObj G'] in
@[reassoc] theorem sqMap_snd : sqMap h ≫ (snd G G).left = (snd G' G').left ≫ φ :=
  congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G')))


end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace tens

variable {X X' : Scheme.{0}} (t : SAB H X) (Λ : Unim E)

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

end tens

section MapRight

variable {S S' : Scheme.{0}} {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
  {G G' A A' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj A] [IsCommMonObj A]
  [GrpObj A'] [IsCommMonObj A'] {G₁ G₁' A₁ A₁' : Over S'} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₁'] [IsCommMonObj G₁']
  [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₁'] [IsCommMonObj A₁']
  {a : OAct O G} {a' : OAct O G'} {b : OAct O A} {b' : OAct O A'} {a₁ : OAct O G₁} {a₁' : OAct O G₁'} {b₁ : OAct O A₁}
  {b₁' : OAct O A₁'}

end MapRight

section Thick

variable {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)

@[reassoc] theorem thickMap_fst (G : Over (Sp R)) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc] theorem thickMap_snd (G : Over (Sp R)) :
    thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) = pullback.snd G.hom (thick R I e) ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

end Thick

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t) (Λ : Unim E)

def abPartAct : OAct (𝓞 E) U.D.toPre.P.A := letI := H.starRing; ofRingAct U.oD.onB.toRingAct

abbrev abTens : Over (Sp R) := Λ.obj (abPartAct U)

theorem isLinearHom_q (e : ℕ) : IsLinearHom (t.act.pullback (thick R I e) _) ((abPartAct U).pullback (thick R I e) _)
    (U.U.gt e).q :=
  letI := H.starRing
  ⟨(U.U.gt e).q_hom, fun c => U.lin.q_lin e c⟩

def qTens (e : ℕ) : thickObj R I e (tens t Λ).G ⟶ thickObj R I e (abTens U Λ) :=
  ((tens.isTensor t Λ).pullback (thick R I e)).mapRight ((Λ.isTensor (abPartAct U)).pullback (thick R I e))
    (isLinearHom_q U e)

end Unif

section Point

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) (Λ : Unim E)

def defIdeal : Ideal ↥(intO ↥C.S) := (maximalIdeal A.R).map A.f

abbrev gPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (tens A.t Λ).G

abbrev bPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (abTens A.U Λ)

abbrev gtLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (gPt A Λ)

abbrev bLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (bPt A Λ)

def levToDat (G : Over (Sp A.R)) (e : ℕ) : (thickObj _ (defIdeal A) e ((Over.pullback (spMap A.f)).obj G)).left ⟶
    (thickObj A.R (maximalIdeal A.R) e G).left := hMap (φ := A.f) (hφ := le_rfl) G _ (𝟙 _)

theorem isGrpPullback_levToDat (G : Over (Sp A.R)) [GrpObj G] (e : ℕ) :
    IsGrpPullback (thickObj _ (defIdeal A) e ((Over.pullback (spMap A.f)).obj G)) (thickObj A.R (maximalIdeal A.R) e G)
      (sE A.f le_rfl e) (levToDat A G e) :=
  @Out.PullGtPf.isGrpPullback_hMap _ _ _ _ _ _ _ _ A.f le_rfl e G _ _ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _)))

@[reassoc] theorem levToDat_fst (G : Over (Sp A.R)) (e : ℕ) :
    levToDat A G e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst G.hom (spMap A.f) :=
  (Out.PullGtPf.hMap_fst _ _ _).trans (congrArg _ (Category.id_comp _))

def prLev (e : ℕ) : gtLev A Λ e ⟶ bLev A Λ e :=
  Over.homMk ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift (levToDat A _ e ≫ (qTens A.U Λ e).left) (gtLev A Λ e).hom
    (by rw [Category.assoc, Over.w]; exact (isGrpPullback_levToDat A _ e).1.w))
    ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift_snd _ _ _)

@[reassoc] theorem prLev_levToDat (e : ℕ) :
    (prLev A Λ e).left ≫ levToDat A _ e = levToDat A _ e ≫ (qTens A.U Λ e).left :=
  (isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift_fst _ _ _

variable {X : Scheme.{0}} {π : X ⟶ Y.X} {t : SAB H X} (m : SABMap t Y.t π) (z : Sp ↥(intO ↥C.S) ⟶ X) (hz : z ≫ π = P.yt)


end Point

section Generic

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} (Z : Mdl Y i₀)

end Generic

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

variable (ct : At S κ p) (Λ : (uniTrue ct).Unim)

end Record

end GlobalTheory.LocM
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle =====
