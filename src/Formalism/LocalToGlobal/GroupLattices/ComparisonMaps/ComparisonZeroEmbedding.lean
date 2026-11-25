module

public import Formalism.LocalRingCardinality.DataKerP
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK, Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding

-- ===== clump member: Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK =====
-- clump-header: {"m": "Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataKerP\npublic import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.L2.G.Cmp

section Maps

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure CmpMaps where
  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  li : ∀ j, j ≤ D.R.m → LinearIndependent (D.gat u w h).Kf
    fun a => cmp j (((Tw.fm u (D.what₂.muAt w)).lat j).b a)

variable {c Tw u w h Lv}

variable (Tw u w) in
def KLx (j : ℕ) : ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₗ[D.what₂.LL] ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V :=
  ratMap ((Tw.fm u (D.what₂.muAt w)).emb j) ((Tw.fm u (D.what₂.muAt w)).emb (j + 1))
    ((Tw.fm u (D.what₂.muAt w)).emb_inj (j + 1)) ((D.chTw u (D.what₂.muAt w)).Klin j)

open Classical in
def chainFirst (M : CmpMaps c Tw u w h Lv) : Chain Lv where
  Kz j := if hj : j < D.R.m then
      extK (M.cmp j) (M.cmp (j + 1)) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj.le) (KLx Tw u w j)
    else 0

end Maps

section Vram

variable {D : D7} (c : LatCmp D)

def vramC (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn :=
  (Submodule.span (D.gat u w hg).Kf
    (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))).restrictScalars (D.gat u w hg).O

end Vram

end Formalism.L2.G.Cmp

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK =====

-- ===== clump member: Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding =====
-- clump-header: {"m": "Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding", "h": "module\n\npublic import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.L2.G.Cmp

section Zero

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

def cmpSl : ((D.fm u).lat 0).V →ₛₗ[c.embW u w h] (D.gat u w h).Fn where
  toFun := c.cmp u w h
  map_add' := (c.cmp u w h).map_add
  map_smul' := c.cmp_smul u w h

def cmpZero : ((Tw.fm u (D.what₂.muAt w)).lat 0).V →ₛₗ[c.embW u w h] (D.gat u w h).Fn :=
  (cmpSl c u w h).comp (Tw.e0 u (D.what₂.muAt w)).symm.toLinearMap

private theorem linearIndependent_semilinear_basis_of_basis {K L V W κ κ' : Type*} [Field K] [Field L] {σ : K →+* L} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module L W] [Fintype κ] [Fintype κ'] (B : Module.Basis κ K V)
    (B' : Module.Basis κ' K V) (φ : V →ₛₗ[σ] W) (hB : LinearIndependent L (φ ∘ B)) :
    LinearIndependent L (φ ∘ B') := by
  rw [linearIndependent_iff_card_eq_finrank_span] at hB ⊢
  have hs : Submodule.span L (Set.range (φ ∘ B')) = Submodule.span L (Set.range (φ ∘ B)) := by
    refine le_antisymm ?_ ?_ <;> rw [Submodule.span_le, Set.range_comp, Set.range_comp]
    · exact (Set.image_mono fun x _ => by rw [SetLike.mem_coe, B.span_eq]; trivial).trans
        (Submodule.image_span_subset_span φ _)
    · exact (Set.image_mono fun x _ => by rw [SetLike.mem_coe, B'.span_eq]; trivial).trans
        (Submodule.image_span_subset_span φ _)
  unfold Set.finrank at hB ⊢
  rw [hs, ← hB]
  exact Fintype.card_congr (B'.indexEquiv B)

theorem cmpZero_li : LinearIndependent (D.gat u w h).Kf
    fun a => cmpZero c Tw u w h (((Tw.fm u (D.what₂.muAt w)).lat 0).b a) := by
  have e : (fun a => cmpZero c Tw u w h (((Tw.fm u (D.what₂.muAt w)).lat 0).b a)) =
      cmpSl c u w h ∘ (((Tw.fm u (D.what₂.muAt w)).lat 0).b.map (Tw.e0 u (D.what₂.muAt w)).symm) := by
    funext a
    simp [cmpZero]
  rw [e]
  exact linearIndependent_semilinear_basis_of_basis ((D.fm u).lat 0).b _ (cmpSl c u w h) (c.5 u w h)

end Zero

section Up

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure CmpUp where
  cmpS : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1)
  liS : ∀ j, j + 1 ≤ D.R.m → LinearIndependent (D.gat u w h).Kf
    fun a => cmpS j (((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).b a)

variable {c Tw u w h Lv}

def CmpUp.cmp (S : CmpUp c Tw u w h Lv) :
    (j : ℕ) → ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  | 0 => cmpZero c Tw u w h
  | j + 1 => S.cmpS j

def CmpUp.maps (S : CmpUp c Tw u w h Lv) : CmpMaps c Tw u w h Lv where
  cmp := S.cmp
  li := fun j hj => match j, hj with
    | 0, _ => cmpZero_li c Tw u w h
    | j + 1, hj => S.liS j hj

end Up

structure KerData (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime]
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl) where
  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m
  lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]
  iLL_lam : ∀ (x : D.what₂.LL) (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ),
    iK (c.embW u w h x) = lam ⟨D.what₂.embLL x, hx⟩
  iw : ∀ j (v : Fin (Fl.Pj j).nV), D.host.E →+* (Fl.Pj j).Qq v
  glob : ∀ j, Lv.comp j → (Fl.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((Fl.Pj j).m + 1) → D.host.E)
  glob_loc : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → ∀ v,
    L v = Submodule.span ((Fl.Pj j).W v) {y | ∃ x ∈ glob j a L, y = fun i => iw j v (x i)}
  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u (D.what₂.muAt w)).cls j
  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u (D.what₂.muAt w)).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x
  Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
    MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]
  up : CmpUp c Tw u w h Lv
  intS : ∀ j, j + 1 ≤ D.R.m → Submodule.span (D.gat u w h).O
    (up.cmpS j '' (((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).L : Set ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V)) =
      Lv.Int (j + 1)

def kerAtP_of {D : D7} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (K : KerData D c Tw u w h Lv) : LocalToGlobal₂ D Gt c Tw u w h (chainFirst K.up.maps) where
  fl_t := K.fl_t
  fl_m := K.fl_m
  lam := K.lam
  iK := K.iK
  iw := K.iw
  glob := K.glob
  cls := K.cls
  Th := K.Th
  cmp := K.up.maps.cmp

def withFirst {D : D7} (c : LatCmp D) (Tw : TwForms D) (Y : LatInst D)
    (M : ∀ u w hg, CmpMaps c Tw u w hg (Y.Lv u w hg)) : LatInst D :=
  { Y with Ch := fun u w hg => chainFirst (M u w hg), Vram := vramC c }

theorem withFirst_vram {D : D7} (c : LatCmp D) (Tw : TwForms D) (Y : LatInst D)
    (M : ∀ u w hg, CmpMaps c Tw u w hg (Y.Lv u w hg)) : c.VramDef (withFirst c Tw Y M) := by
  intro u w hg
  first
    | rfl

def kerAll {D : D7} (hT : GatTies D) (c : LatCmp D) (Tw : TwForms D) (Y : LatInst D)
    (K : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      KerData D c Tw u w h (Y.Lv u w h)) :
    ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      LocalToGlobal₂ D hT c Tw u w h ((withFirst c Tw Y fun u w h =>
        haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
        (K u w h).up.maps).Ch u w h) :=
  fun u w h =>
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    kerAtP_of hT (K u w h)

end Formalism.L2.G.Cmp

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding =====
