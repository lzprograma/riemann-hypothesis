module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcIotaInj
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcCGNonneg

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GrowthExclusionSumEq, Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcModsub, Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NumericalClosedOfNeed

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GrowthExclusionSumEq =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GrowthExclusionSumEq", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcIotaInj\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_capU (j : ℕ) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (k : ℕ) :
    Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) k =
      nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s k) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.capU nc_zc
  rw [nc_partner hg]
  have key : ∀ a : ℕ, t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + k • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      t0 + ((a + k) % (D.gat u w hg).P.n' (Y.vOf u w hg t0)) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) := by
    intro a
    rw [hn, mod_addOrderOf_nsmul, add_nsmul, add_assoc]
  exact congrArg (fun t => Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t) + Formalism.MainNotions.G.cG L) (key s.val)

open Classical in
include hL ht0 in
theorem nc_gU_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      Formalism.MainNotions.FormalGroupSystem.gam (D.what₂.places.resChar w) * ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), nc_ya X Y u w hg t0 s -
        ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos, ∑' e : ℕ,
          min (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1))
            (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.gU
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h), Finset.filter_image,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf]
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  rw [nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

open Classical in
include hL ht0 in
theorem growth_exclusion_sum_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), ∑' e : ℕ,
        (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w)
            (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) then 0 else
          max 0 (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1) -
            nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.g0
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have e1 : ∀ e : ℕ, (if Odd e ∧ ¬ Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e) else 0) =
      (if Odd e then (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then 0 else
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e)) else 0) := by
    intro e
    by_cases h1 : Odd e <;> by_cases h2 : Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e <;>
      simp [h1, h2]
  rw [tsum_congr e1, nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GrowthExclusionSumEq =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcModsub =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcModsub", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcIotaInj\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_modsub (a b e' n : ℕ) (ha : a < n) (hb : b < n) (he : e' < n) (h : (a + e') % n = b) :
    (b + n - a) % n = e' := by
  rcases Nat.lt_or_ge (a + e') n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    subst h
    have : a + e' + n - a = e' + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  · have h2 : (a + e') % n = a + e' - n := by
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    rw [h2] at h
    subst h
    have : a + e' - n + n - a = e' := by omega
    rw [this, Nat.mod_eq_of_lt he]

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_shift (s s' : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ) :
    nc_iota Y u w hg t0 s + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' ↔
      (s.val + e) % (D.gat u w hg).P.n' (Y.vOf u w hg t0) = s'.val := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have key : ∀ (a b : ℕ), b < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) →
      (t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
        t0 + b • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ↔
      (a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) = b) := by
    intro a b hb
    have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by omega
    rw [add_assoc, ← add_nsmul, show (a + e) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      ((a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) by
        rw [mod_addOrderOf_nsmul]]
    constructor
    · intro h
      exact nsmul_injOn_Iio_addOrderOf (show (a + e) % _ ∈ Set.Iio _ from Nat.mod_lt _ hpos)
        (show b ∈ Set.Iio _ from hb) (add_left_cancel h)
    · intro h; rw [h]
  have := key s.val s'.val (by rw [← hn]; exact s'.isLt)
  rw [← hn] at this
  exact this

include hL ht0 in
theorem nc_excl (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ)
    (he : 2 * e + 1 ∈ dSet ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) s) :
    Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) := by
  have hloc := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold dSet at he
  obtain ⟨s', hs', hd⟩ := Finset.mem_image.1 he
  rw [Finset.mem_filter] at hs'
  have hpos : 0 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by have := s.isLt; omega
  have hlt : 2 * e + 1 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by rw [← hd]; exact Nat.mod_lt _ hpos
  have hne : s' ≠ s := fun h => hs'.2 (by rw [h])
  refine ⟨⟨e, rfl⟩, nc_iota Y u w hg t0 s', ((hloc s').2.1).1 hs'.1, fun h => hne (hinj h), ?_⟩
  refine ⟨by omega, ?_, ?_⟩
  · rw [nc_partner hg]
    congr 1
    show nc_iota Y u w hg t0 s + (2 * e + 1) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s'
    refine (nc_shift X Y hT hL u w hg t0 ht0 s s' (2 * e + 1)).2 ?_
    rw [← hd]
    have := s.isLt
    have := s'.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : s.val + (s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) - s.val) =
        s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt s'.isLt]
  · intro e' he0 he1 hp
    rw [nc_partner hg] at hp
    have hp' : nc_iota Y u w hg t0 s + e' • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' :=
      (Prod.mk.inj hp).2
    have h1 := (nc_shift X Y hT hL u w hg t0 ht0 s s' e').1 hp'
    have h2 := nc_modsub s.val s'.val e' _ s.isLt s'.isLt (by omega) h1
    rw [hd] at h2
    omega

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcModsub =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NumericalClosedOfNeed =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NumericalClosedOfNeed", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GrowthExclusionSumEq\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcCGNonneg\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcModsub\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

open Classical in
theorem nc_loc (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    nc_Loc D L X Y K hT u w hg t0 j := by
  obtain ⟨hal, hal0, hcap, hcap0⟩ := nc_ties X Y hT hL u w hg t0 ht0 j hj
  exact ⟨nc_gU_eq X Y hT hL u w hg t0 ht0 K j, growth_exclusion_sum_eq X Y hT hL u w hg t0 ht0 K j,
    hal, hal0, hcap, hcap0, fun s _ e he => nc_excl X Y hT hL u w hg t0 ht0 s e he⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NumericalClosedOfNeed =====
