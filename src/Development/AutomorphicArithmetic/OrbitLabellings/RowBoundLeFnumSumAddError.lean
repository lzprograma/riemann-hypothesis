module

public import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
public import Mathlib.Algebra.BigOperators.Field
public import Formalism.DropLevelBounds.ThBounds
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
public import Mathlib.Analysis.Complex.ExponentialBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProof
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.OrbitLabellings.AttainsBlockListOfWeightsAlongOrbits, Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError

-- ===== clump member: Development.AutomorphicArithmetic.OrbitLabellings.AttainsBlockListOfWeightsAlongOrbits =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.OrbitLabellings.AttainsBlockListOfWeightsAlongOrbits", "h": "module\n\npublic import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.GroupTheory.Nilpotent\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Mathlib.Algebra.BigOperators.Field\n\n"}
section -- clump:auto
@[expose] public section

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2

namespace UpperTheory.G2.RowPlan

private theorem cast_eq {d : ℕ} (hd : Odd d) (x y : ℕ) :
    (x : ZMod (2 * d)) = y ↔ x % 2 = y % 2 ∧ (x : ZMod d) = y := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff,
    ← Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_two_left).2 hd)]
  rfl

private theorem ev_iff {d : ℕ} [NeZero d] (hd : Odd d) (ev : ZMod d → ZMod (2 * d))
    (hev : ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a) (s : ZMod (2 * d)) (a : ZMod d) :
    s = ev a ↔ Even s.val ∧ a = ((s.val : ℕ) : ZMod d) := by
  constructor
  · rintro rfl
    exact ⟨(hev a).1, (hev a).2.symm⟩
  · rintro ⟨he, ha⟩
    haveI : NeZero (2 * d) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne d)⟩
    have key : ((s.val : ℕ) : ZMod (2 * d)) = (((ev a).val : ℕ) : ZMod (2 * d)) := by
      rw [cast_eq hd]
      exact ⟨by rw [Nat.even_iff.1 he, Nat.even_iff.1 (hev a).1], by rw [(hev a).2, ha]⟩
    simpa only [ZMod.natCast_zmod_val] using key

private theorem cast_val_eq_castHom_of_double {d : ℕ} [NeZero d] (x : ZMod (2 * d)) :
    ((x.val : ℕ) : ZMod d) = ZMod.castHom (dvd_mul_left d 2) (ZMod d) x := by
  haveI : NeZero (2 * d) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne d)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem cast_val_two_eq_castHom_of_double {d : ℕ} [NeZero d] (x : ZMod (2 * d)) :
    ((x.val : ℕ) : ZMod 2) = ZMod.castHom (dvd_mul_right 2 d) (ZMod 2) x := by
  haveI : NeZero (2 * d) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne d)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem ev_iff' {d : ℕ} [NeZero d] (hd : Odd d) (ev : ZMod d → ZMod (2 * d))
    (hev : ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a) (s : ZMod (2 * d)) (a : ZMod d) (i : ℕ)
    (hi : Odd i) :
    s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) ↔
      Even s.val ∧ a = ((s.val : ℕ) : ZMod d) - (i : ZMod d) := by
  have h1 : s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) ↔ s + (d : ZMod (2 * d)) - i = ev a := by
    constructor
    · intro h
      rw [h, add_sub_cancel_right]
    · intro h
      rw [← h, sub_add_cancel]
  rw [h1, ev_iff hd ev hev]
  have hpar : Even (s + (d : ZMod (2 * d)) - i).val ↔ Even s.val := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even, cast_val_two_eq_castHom_of_double, cast_val_two_eq_castHom_of_double, map_sub,
      map_add, map_natCast, map_natCast, ZMod.natCast_eq_one_iff_odd.2 hd, ZMod.natCast_eq_one_iff_odd.2 hi,
      add_sub_cancel_right]
  have hres : (((s + (d : ZMod (2 * d)) - i).val : ℕ) : ZMod d) = ((s.val : ℕ) : ZMod d) - i := by
    rw [cast_val_eq_castHom_of_double, cast_val_eq_castHom_of_double, map_sub, map_add (f := _), map_natCast, map_natCast, ZMod.natCast_self, add_zero]
  rw [hpar, hres]

variable {d : ℕ} [NeZero d]

private noncomputable def supp (y : ZMod d → ℕ → ℕ) : Finset (ZMod d × ℕ) :=
  (Finset.univ ×ˢ oddLevels d).filter fun x => y x.1 x.2 ≠ 0

private theorem sum_supp {M : Type} [AddCommMonoid M] (y : ZMod d → ℕ → ℕ) (f : ZMod d → ℕ → ℕ → M)
    (hf : ∀ a i, f a i 0 = 0) :
    ∑ x ∈ supp y, f x.1 x.2 (y x.1 x.2) = ∑ a, ∑ i ∈ oddLevels d, f a i (y a i) := by
  unfold supp
  rw [Finset.sum_filter_of_ne, Finset.sum_product]
  intro x _ hx hy
  apply hx
  rw [hy, hf]

private theorem card_supp (y : ZMod d → ℕ → ℕ) (M : ℕ) (h : ∀ a i, 2 * M + 1 ≤ i → y a i = 0) :
    (supp y).card ≤ d * M := by
  have hsub : supp y ⊆ Finset.univ ×ˢ ((Finset.range M).image fun j => 2 * j + 1) := by
    intro x hx
    unfold supp at hx
    rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨-, hodd⟩, hy⟩ := hx
    unfold oddLevels at hodd
    rw [Finset.mem_filter] at hodd
    obtain ⟨j, hj⟩ := hodd.2
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, Finset.mem_image.2 ⟨j, Finset.mem_range.2 ?_, hj.symm⟩⟩
    by_contra hjM
    exact hy (h x.1 x.2 (by omega))
  calc (supp y).card ≤ (Finset.univ ×ˢ ((Finset.range M).image fun j => 2 * j + 1)).card :=
        Finset.card_le_card hsub
    _ = d * M := by
      rw [Finset.card_product, Finset.card_univ, ZMod.card,
        Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Finset.card_range]

private noncomputable def rst (n : ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (s : ZMod (2 * d)) : ZMod (2 * d) → ℕ → ℕ :=
  fun a k => if a = s then (if Even s.val ∧ k = n then 0 else ga s k) else 0

variable {C : Type} [Field C] {V : VF C} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

private theorem deg_le (X : RowData C V (2 * d) I J) (n K : ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (s : ZMod (2 * d)) :
    (RF.monDegAll X 0 (rst n ga s) K : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) := by
  unfold RF.monDegAll
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [monDeg, rst, hb]) (by simp)]
  unfold monDeg
  push_cast
  calc ∑ k ∈ Finset.Icc 1 (min K (X.rkF 0 s)), (k : ℝ) * (rst n ga s s k : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (rst n ga s s k : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk ⊢
          exact ⟨hk.1, le_trans hk.2 (min_le_left _ _)⟩
        · intro k _ _
          positivity
    _ = ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [rst, ite_true]
        split_ifs <;> simp
    _ ≤ _ := le_refl _

private noncomputable def blocks (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d)) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K : ℕ) : List (RF.GlobalTheory (2 * d) × ℝ) :=
  ((Finset.univ : Finset (ZMod (2 * d))).toList.map fun s =>
      (RF.GlobalTheory.mon 0 (rst X.n ga s) K, (RF.monDegAll X 0 (rst X.n ga s) K : ℝ) / ((V.l : ℝ) - 1))) ++
  (((Finset.univ : Finset (ZMod d)).toList.map fun a =>
      (RF.GlobalTheory.ch 0 (ev a) (u a), RF.chBd V.l X.n X.m (u a))) ++
    ((supp y).toList.map fun x =>
      (RF.GlobalTheory.bi 0 (ev x.1) x.2 (y x.1 x.2), RF.blockBd V.l X.n X.m x.2 (y x.1 x.2))))

private theorem blocks_rows (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d)) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K M : ℕ) (h : ∀ a i, 2 * M + 1 ≤ i → y a i = 0) :
    ((blocks X ev y u ga K).map fun q => q.1.what₂ X.n).sum ≤ d * ((M + 1) * X.n + 2 * K) := by
  simp only [blocks, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ, ZMod.card]
  have h1 := Nat.mul_le_mul_right X.n (card_supp y M h)
  nlinarith

private theorem blocks_bd (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d)) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K : ℕ) (hl : 2 ≤ V.l) :
    ((blocks X ev y u ga K).map Prod.snd).sum ≤
      ((∑ a, ∑ i ∈ oddLevels d, RF.blockBd V.l X.n X.m i (y a i)) + ∑ a, RF.chBd V.l X.n X.m (u a)) +
        (∑ s : ZMod (2 * d), ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = X.n then (0 : ℝ) else (k : ℝ) * ga s k)) /
          ((V.l : ℝ) - 1) := by
  simp only [blocks, List.map_append, List.sum_append, List.map_map, Function.comp_def, Finset.sum_map_toList]
  have hs := sum_supp y (fun _ i v => RF.blockBd V.l X.n X.m i v) (fun a i => by simp [RF.blockBd])
  have hpos : (0 : ℝ) < (V.l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (V.l : ℝ) := by exact_mod_cast hl
    linarith
  have hD : ∑ s : ZMod (2 * d), (RF.monDegAll X 0 (rst X.n ga s) K : ℝ) / ((V.l : ℝ) - 1) ≤
      (∑ s : ZMod (2 * d), ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = X.n then (0 : ℝ) else (k : ℝ) * ga s k)) /
        ((V.l : ℝ) - 1) := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => deg_le X X.n K ga s) hpos.le
  linarith

private theorem blocks_wt (hd : Odd d) (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d))
    (hev : ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K : ℕ) (hK : X.n + (X.j + X.j') ≤ K) (W : ZMod d → ℕ)
    (hs : ∀ s k, ga s k ≠ 0 → 1 ≤ k ∧ k ≤ X.rkF 0 s)
    (hm : ∀ s : ZMod (2 * d), Even s.val → ga s X.n = W ((s.val : ℕ) : ZMod d))
    (hb : ∀ a, W a = (∑ i ∈ oddLevels d, V.l ^ i * y a i) + (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) + u a)
    (s : ZMod (2 * d)) (k : ℕ) :
    ((blocks X ev y u ga K).map fun q => q.1.wt X 0 s k + q.1.wt X 1 (s + (d : ZMod (2 * d))) k).sum = ga s k := by
  have hrk : ∀ a, X.rkF 0 a ≤ K := fun a => le_trans (GlobalTheory.PlanValue.rk_le X 0 a) hK
  simp only [blocks, List.map_append, List.sum_append, List.map_map]
  rw [Finset.sum_map_toList, Finset.sum_map_toList, Finset.sum_map_toList]
  simp [RF.GlobalTheory.wt, rst]
  have hfirst : (if 1 ≤ k ∧ k ≤ K ∧ k ≤ X.rkF 0 s then ga s k else 0) = ga s k := by
    split_ifs with h
    · rfl
    · by_contra hne
      have h' := hs s k (Ne.symm hne)
      exact h ⟨h'.1, le_trans h'.2 (hrk s), h'.2⟩
  have hodd : ∀ i ∈ oddLevels d, Odd i := by
    intro i hi
    unfold oddLevels at hi
    exact (Finset.mem_filter.1 hi).2
  by_cases hkn : k = X.n
  swap
  · simp only [hkn, and_false, ite_false, Finset.sum_const_zero, add_zero]
    exact hfirst
  subst hkn
  simp only [and_true]
  by_cases he : Even s.val
  · have hch : ∀ a, (s = ev a ↔ a = ((s.val : ℕ) : ZMod d)) := fun a => by
      rw [ev_iff hd ev hev s a]
      simp [he]
    have hbi : ∀ a (i : ℕ), Odd i →
        (s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) ↔ a = ((s.val : ℕ) : ZMod d) - (i : ZMod d)) :=
      fun a i hi => by
        rw [ev_iff' hd ev hev s a i hi]
        simp [he]
    have e1 := sum_supp y (fun a i v => if s = ev a then V.l ^ i * v else 0) (fun a i => by simp)
    have e2 := sum_supp y (fun a i v => if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then v else 0)
      (fun a i => by simp)
    rw [Finset.sum_add_distrib, e1, e2]
    have t0 : (if 1 ≤ X.n ∧ X.n ≤ K ∧ X.n ≤ X.rkF 0 s then (if Even s.val then 0 else ga s X.n) else 0) = 0 := by
      simp [he]
    have t1 : (∑ x, if s = ev x then u x else 0) = u ((s.val : ℕ) : ZMod d) := by
      simp_rw [hch]
      simp
    have t2 : (∑ a, ∑ i ∈ oddLevels d, if s = ev a then V.l ^ i * y a i else 0) =
        ∑ i ∈ oddLevels d, V.l ^ i * y ((s.val : ℕ) : ZMod d) i := by
      simp_rw [hch]
      rw [Finset.sum_comm]
      simp
    have t3 : (∑ a, ∑ i ∈ oddLevels d, if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then y a i else 0) =
        ∑ i ∈ oddLevels d, y (((s.val : ℕ) : ZMod d) - (i : ZMod d)) i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [hbi _ i (hodd i hi)]
      simp
    rw [t0, t1, t2, t3, hm s he, hb]
    ring
  · have hch0 : ∀ a, ¬ s = ev a := fun a h => he (by rw [h]; exact (hev a).1)
    have t3 : (∑ a, ∑ i ∈ oddLevels d, if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then y a i else 0) = 0 :=
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun i hi =>
        ite_eq_right (fun h => he ((ev_iff' hd ev hev s a i (hodd i hi)).1 h).1)))
    have e2 := sum_supp y (fun a i v => if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then v else 0)
      (fun a i => by simp)
    rw [Finset.sum_add_distrib, e2, t3]
    simpa [hch0, he] using hfirst

end UpperTheory.G2.RowPlan

open UpperTheory.G2.RowPlan in
theorem UpperTheory.attains_blockListOfWeights_along_orbits :
    RF.CHSupply → RF.MONSupply → ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), Fintype.card P.Pl = P.f → 1 ≤ P.m → P.m + 3 ≤ P.k → P.r = P.k - 1 + P.m → 5 ≤ l →
    ∀ (Pk : PkgCs P l C1) (y : P.Pl → ZMod P.d → ℕ → ℕ) (u : P.Pl → ZMod P.d → ℕ) (ev : ZMod P.d → ZMod (2 * P.d)),
    (∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod P.d) = a) →
    (∀ z ∈ Pk.Z, ∀ a, RF.alongOrb P z Pk.W a = (∑ i ∈ oddLevels P.d, l ^ i * y z a i) +
      (∑ i ∈ oddLevels P.d, y z (a - (i : ZMod P.d)) i) + u z a) →
    (∀ z ∈ Pk.Z, ∀ a i, RF.i0 P.k l ≤ i → y z a i = 0) →
    (∀ (o : {z // z ∈ Pk.Z}) a, ∀ i ∈ oddLevels P.d, y o.1 a i ≠ 0 →
      (RF.GlobalTheory.bi 0 (ev a) i (y o.1 a i)).Attains (Pk.R.X o) (Pk.R.F o) (RF.blockBd l (P.k - 1) P.m i (y o.1 a i))) →
    Pk.ν ≤ (∑ z ∈ Pk.Z, ((∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y z a i)) + ∑ a, RF.chBd l (P.k - 1) P.m (u z a))) +
      Pk.rest / ((l : ℝ) - 1) := by
  intro hCH hM P l C1 hf hm1 hmk hr hl5 Pk y u ev hev hW hy hbi
  have hd : Odd P.d := Pk.odd
  have hn1 : ∀ o, (Pk.R.X o).n = P.k - 1 := fun o => (Pk.R.hn o).1
  have hn2 : ∀ o, (Pk.R.X o).m = P.m := fun o => (Pk.R.hn o).2
  have hVl : Pk.R.V.l = l := Pk.R.hVl
  obtain ⟨M, hMe⟩ : Odd (RF.i0 P.k l) := (GlobalTheory.LevelsOrbits.thlEq P.k l (by lia) (by lia)).1
  let L : ↥Pk.Z → List (RF.GlobalTheory (2 * P.d) × ℝ) := fun o =>
    blocks (Pk.R.X o) ev (y o.1) (u o.1) (Pk.ga o) P.r
  have hv := Pk.val L ?_ ?_ ?_ ?_
  · refine le_trans hv ?_
    calc ∑ o, (List.map Prod.snd (L o)).sum
        ≤ ∑ o : ↥Pk.Z, (((∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y o.1 a i)) +
            ∑ a, RF.chBd l (P.k - 1) P.m (u o.1 a)) +
            (∑ s : ZMod (2 * P.d), ∑ k ∈ Finset.Icc 1 P.r,
              (if Even s.val ∧ k = P.k - 1 then (0 : ℝ) else (k : ℝ) * Pk.ga o s k)) / ((l : ℝ) - 1)) := by
          apply Finset.sum_le_sum
          intro o _
          have := blocks_bd (Pk.R.X o) ev (y o.1) (u o.1) (Pk.ga o) P.r (by rw [hVl]; omega)
          rwa [hn1 o, hn2 o, hVl] at this
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, Pk.rest_eq]
          congr 1
          exact Finset.sum_coe_sort Pk.Z (fun z => (∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y z a i)) +
            ∑ a, RF.chBd l (P.k - 1) P.m (u z a))
  · intro o q hq
    simp only [L, blocks, List.mem_append, List.mem_map, Finset.mem_toList] at hq
    rcases hq with ⟨s, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨x, hx, rfl⟩
    · exact (hM _ _ _ _ _ (Pk.R.X o) (Pk.R.F o) 0 _ P.r).1
    · have hbig : (Pk.R.X o).big 0 (ev a) := ((Pk.R.alt o).2 (ev a)).2 (hev a).1
      exact (hCH _ _ _ _ _ (Pk.R.X o) (Pk.R.F o) 0 (ev a) hbig (u o.1 a)).1 (Pk.R.alt o)
    · simp only [supp, Finset.mem_filter, Finset.mem_product] at hx
      have := hbi o x.1 x.2 hx.1.2 hx.2
      rwa [hn1 o, hn2 o, hVl]
  · intro o q hq g e N hqe
    simp only [L, blocks, List.mem_append, List.mem_map, Finset.mem_toList] at hq
    rcases hq with ⟨s, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨x, hx, rfl⟩
    · obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hqe
      exact ⟨s, fun a k ha => by simp [rst, ha]⟩
    · cases hqe
    · cases hqe
  · have hrow : ∀ o, (List.map (fun q => RF.GlobalTheory.what₂ (Pk.R.X o).n q.1) (L o)).sum ≤
        P.d * ((M + 1) * (P.k - 1) + 2 * P.r) := by
      intro o
      have := blocks_rows (Pk.R.X o) ev (y o.1) (u o.1) (Pk.ga o) P.r M
        (fun a i hi => hy o.1 o.2 a i (by omega))
      rw [hn1 o] at this
      rw [hn1 o]
      exact this
    have hZ := GlobalTheory.PlanValue.card_reps P Pk.Z Pk.hZ
    rw [hf] at hZ
    calc 2 * ∑ o, (List.map (fun q => RF.GlobalTheory.what₂ (Pk.R.X o).n q.1) (L o)).sum
        ≤ 2 * ∑ o : ↥Pk.Z, P.d * ((M + 1) * (P.k - 1) + 2 * P.r) := by
          gcongr with o
          exact hrow o
      _ = P.f * ((RF.i0 P.k l + 1) * (P.k - 1) + 4 * P.r) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, ← hZ, hMe]
          ring
      _ ≤ Pk.nW := Pk.what₂
  · intro o s k
    have hK : (Pk.R.X o).n + ((Pk.R.X o).j + (Pk.R.X o).j') ≤ P.r := by
      have e : (Pk.R.X o).m = (Pk.R.X o).j + (Pk.R.X o).j' := rfl
      rw [← e, hn1 o, hn2 o]
      omega
    exact blocks_wt hd (Pk.R.X o) ev hev (y o.1) (u o.1) (Pk.ga o) P.r hK
      (fun a => RF.alongOrb P o.1 Pk.W a) (Pk.supp o)
      (fun s hs => by
        rw [hn1 o, Pk.main o s hs]
        simp only [RF.alongOrb, ZMod.val_natCast])
      (fun a => by
        rw [hVl]
        exact hW o.1 o.2 a) s k
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.OrbitLabellings.AttainsBlockListOfWeightsAlongOrbits =====

-- ===== clump member: Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError", "h": "module\n\npublic import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs\npublic import Formalism.DropLevelBounds.ThBounds\npublic import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic\npublic import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe\npublic import Development.AutomorphicArithmetic.OrbitLabellings.AttainsBlockListOfWeightsAlongOrbits\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\npublic import Mathlib.Analysis.Complex.ExponentialBounds\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2

namespace UpperTheory.G2.RowBd

private theorem exists_ev (d : ℕ) [NeZero d] (hd : Odd d) :
    ∃ ev : ZMod d → ZMod (2 * d), ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a := by
  have h : ∀ a : ZMod d, ∃ s : ZMod (2 * d), Even s.val ∧ ((s.val : ℕ) : ZMod d) = a := by
    intro a
    have ha := ZMod.val_lt a
    by_cases he : Even a.val
    · refine ⟨(a.val : ℕ), ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      exact ⟨he, ZMod.natCast_zmod_val a⟩
    · refine ⟨(a.val + d : ℕ), ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      refine ⟨(Nat.not_even_iff_odd.1 he).add_odd hd, ?_⟩
      rw [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  choose ev hev using h
  exact ⟨ev, hev⟩

end UpperTheory.G2.RowBd

open UpperTheory.G2.RowBd GlobalTheory.GoodDepth GlobalTheory.InertContent in
theorem UpperTheory.rowBound_le_Fnum_sum_add_error :
    RF.BiSupply → RF.CHSupply → RF.MONSupply → ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (P : RF.Par) (l : ℕ),
    Fintype.card P.Pl = P.f → 1 ≤ P.m → P.m + 3 ≤ P.k → P.r = P.k - 1 + P.m → 0 ≤ P.SE → l.Prime → 5 ≤ l → ∀ Pk : PkgCs P l C1,
    Pk.T * Pk.ν ≤ (∑ z ∈ Pk.Z, Fnum l P.d fun s => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w s) +
      Cc * (Real.log P.k * P.m * (∑ z, P.w z) / l + P.f * P.k * P.SE / l + P.k * thl P.k l * (∑ z, P.w z) +
        Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by
  intro hBi hCH hMON C1 hC1
  refine ⟨3567 + 6 * C1, by linarith, ?_⟩
  intro P l hcard hm hmk hr hSE hlp hl Pk
  have := P.nz
  obtain ⟨ev, hev⟩ := exists_ev P.d Pk.odd
  have hdeg := Pk.deg
  have hk1 : 1 ≤ P.k - 1 := by omega
  have hex : ∀ o : ↥Pk.Z, ∃ p : Plan l P.d (RF.alongOrb P o Pk.W),
      (∀ a i, RF.i0 P.k l ≤ i → p.y a i = 0) ∧
      (∀ a i, p.y a i ≠ 0 → p.y a i ∈ {y : ℕ | RF.GlobalTheory.Attains (Pk.R.X o) (Pk.R.F o)
        (RF.GlobalTheory.bi 0 (ev a) i y) (RF.blockBd l (P.k - 1) P.m i y)}) ∧
      Pk.T * p.bound (P.k - 1) P.m ≤ Fnum l P.d (fun a => ((P.k : ℝ) - 1) * RF.alongOrb P o P.w a) +
        (32 * Real.log P.k * P.m / l + P.k * thl P.k l) * (∑ a, RF.alongOrb P o P.w a) +
        P.d * (4 * P.k * (C1 * P.SE) / l + 3535 * Pk.T * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by
    intro o
    refine orbit l P.d hl P.m P.k hmk hm (RF.alongOrb P o Pk.W) (RF.alongOrb P o P.w) Pk.T Pk.θ0
      (C1 * P.SE) hdeg.T_one (fun a => hdeg.w_pos _) (fun a => hdeg.TW_lo _) (fun a => hdeg.TW_hi _)
      (mul_nonneg hC1 hSE) hdeg.th_rng hdeg.th_m _ ?_
    intro a i hi hlt
    have hiodd := Finset.mem_filter.mp hi
    have hid : i < P.d := Finset.mem_range.mp hiodd.1
    have halt := Pk.R.alt o
    have hW := hBi Pk.R.C Pk.R.V (2 * P.d) (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) halt
      (by rw [Pk.R.hVl]; exact hl) (by rw [(Pk.R.hn o).1]; exact hk1) 0 (ev a)
      ((halt.2 (ev a)).mpr (hev a).1) i hiodd.2 (by omega)
    rw [Pk.R.hVl, (Pk.R.hn o).1, (Pk.R.hn o).2] at hW
    refine ⟨hW.1, fun Y0 => ?_⟩
    obtain ⟨y, hy, h1, h2⟩ := hW.2 Y0
    have hmono := mono_resι_var l (P.k - 1) hlt.le
    exact ⟨y, hy, h1, by omega⟩
  choose pl hpl using hex
  let y : P.Pl → ZMod P.d → ℕ → ℕ := fun z => if h : z ∈ Pk.Z then (pl ⟨z, h⟩).y else fun _ _ => 0
  let u : P.Pl → ZMod P.d → ℕ := fun z => if h : z ∈ Pk.Z then (pl ⟨z, h⟩).u else fun _ => 0
  have hν := UpperTheory.attains_blockListOfWeights_along_orbits hCH hMON P l C1 hcard hm hmk hr hl Pk y u ev hev
    (by
      intro z hz a
      simp only [y, u, dite_eq_left hz]
      exact (pl ⟨z, hz⟩).bal a)
    (by
      intro z hz a i hi
      simp only [y, dite_eq_left hz]
      exact (hpl ⟨z, hz⟩).1 a i hi)
    (by
      intro o a i _ hne
      simp only [y, dite_eq_left o.2] at hne ⊢
      exact (hpl o).2.1 a i hne)
  have hsum : ∑ z ∈ Pk.Z, ((∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y z a i)) +
      ∑ a, RF.chBd l (P.k - 1) P.m (u z a)) = ∑ o : ↥Pk.Z, (pl o).bound (P.k - 1) P.m := by
    rw [← Finset.sum_coe_sort Pk.Z]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [y, u, dite_eq_left o.2, Plan.bound]
    rfl
  have hT0 : 0 < Pk.T := by linarith [hdeg.T_one]
  have hbound : Pk.T * Pk.ν ≤ ∑ o : ↥Pk.Z, Pk.T * (pl o).bound (P.k - 1) P.m +
      Pk.T * Pk.rest / ((l : ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_left hν hT0.le
    rw [hsum, mul_add, Finset.mul_sum] at this
    rw [mul_div_assoc]
    exact this
  have hle := Finset.sum_le_sum (fun o (_ : o ∈ (Finset.univ : Finset ↥Pk.Z)) => (hpl o).2.2)
  set A : ℝ := 32 * Real.log P.k * P.m / l + P.k * thl P.k l with hA
  set X : ℝ := 4 * P.k * (C1 * P.SE) / l + 3535 * Pk.T * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2 with hX
  have hreps := sum_reps P Pk.Z Pk.hZ P.w
  have hcnt := sum_reps P Pk.Z Pk.hZ (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at hcnt
  have hZd : ∑ o : ↥Pk.Z, ((P.d : ℝ) * X) = P.f * X := by
    rw [Finset.sum_coe_sort Pk.Z (fun _ => (P.d : ℝ) * X), ← Finset.sum_mul]
    congr 1
    rw [← hcard]
    simpa using hcnt
  have hRsum : ∑ o : ↥Pk.Z, (Fnum l P.d (fun a => ((P.k : ℝ) - 1) * RF.alongOrb P o P.w a) +
      A * (∑ a, RF.alongOrb P o P.w a) + P.d * X) =
      (∑ z ∈ Pk.Z, Fnum l P.d (fun s => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w s)) +
        A * (∑ z, P.w z) + P.f * X := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hZd, ← Finset.mul_sum,
      Finset.sum_coe_sort Pk.Z (fun z => Fnum l P.d (fun s => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w s)),
      Finset.sum_coe_sort Pk.Z (fun z => ∑ a, RF.alongOrb P z P.w a)]
    simp only [RF.alongOrb] at hreps ⊢
    rw [hreps]
  rw [hRsum] at hle
  have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hrest : Pk.T * Pk.rest / ((l : ℝ) - 1) ≤ C1 * (P.f * P.k * P.SE) * (2 * (l : ℝ)⁻¹) := by
    rw [div_eq_mul_inv]
    have hinv := (inv_le hl).1
    have hCn : 0 ≤ C1 * (P.f * P.k * P.SE) := by positivity
    calc Pk.T * Pk.rest * ((l : ℝ) - 1)⁻¹ ≤ C1 * (P.f * P.k * P.SE) * ((l : ℝ) - 1)⁻¹ :=
          mul_le_mul_of_nonneg_right hdeg.rest_le (inv_nonneg.mpr hl0.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hCn
  have hk4 : (1 : ℝ) ≤ P.k := by exact_mod_cast (show 1 ≤ P.k by omega)
  have hw : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (hdeg.w_pos z).le
  have hthl : 0 ≤ thl P.k l := by
    rw [(GlobalTheory.LevelsOrbits.thlEq P.k l (by omega) (by omega)).2.2.2]
    positivity
  have ha : 0 ≤ Real.log P.k * P.m * (∑ z, P.w z) / l := by positivity
  have hb : 0 ≤ (P.f : ℝ) * P.k * P.SE / l := by positivity
  have hc : 0 ≤ (P.k : ℝ) * thl P.k l * (∑ z, P.w z) := by positivity
  have he : 0 ≤ Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2 := by positivity
  have hid : A * (∑ z, P.w z) + P.f * X + C1 * (P.f * P.k * P.SE) * (2 * (l : ℝ)⁻¹) =
      32 * (Real.log P.k * P.m * (∑ z, P.w z) / l) + 6 * C1 * ((P.f : ℝ) * P.k * P.SE / l) +
        (P.k : ℝ) * thl P.k l * (∑ z, P.w z) + 3535 * (Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by
    rw [hA, hX]
    ring
  nlinarith [mul_nonneg hC1 ha, mul_nonneg hC1 hc, mul_nonneg hC1 he, mul_nonneg hC1 hb]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError =====
