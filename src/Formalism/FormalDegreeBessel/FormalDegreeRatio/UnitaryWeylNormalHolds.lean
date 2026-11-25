module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.MulVecApplyOfRow
public import Formalism.FormalDegreeBessel.StatementG
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.Analysis.Complex.Trigonometric
public import Formalism.SharedLemmas.HpkSq

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.QuantumDeterminants

namespace WeylGroupFacts

variable {k r : ℕ}

def col (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) →
    g i j = if i = j then 1 else 0

def block (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ i j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g i j = if i = j then 1 else 0) ∧
  (∀ i j : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → g i j = if i = j then 1 else 0)

theorem nset_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ col k r g :=
  _root_.WlocSk.UnitaryGroupBasics.nset_iff g

theorem col_one : col k r (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
  intro i j _ _
  exact Matrix.one_apply

theorem col_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : col k r (g * h) :=
  _root_.WlocSk.UnitaryGroupBasics.col_mul hg hh

theorem col_of_left_inv {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hm : g' * g = 1) : col k r g' :=
  _root_.WlocSk.UnitaryGroupBasics.col_of_left_inv hg hm

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hm := m.isLt
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (tau k r i)]
  · rw [hpk_row, ite_eq_left rfl]
  · intro p hp
    rw [hpk_row, ite_eq_right hp, zero_mul]

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau, Fin.val_mk]
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  have hi := i.isLt
  simp only [sgn, tau, Fin.val_mk]
  split_ifs <;> first | rfl | omega

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  first
  | exact _root_.Formalism.SharedLemmas.upq_hpk_mul_self
  | (apply _root_.Formalism.SharedLemmas.upq_hpk_mul_self <;> assumption)

theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det :=
  _root_.WlocSk.UnitaryGroupBasics.isUnit_of_uh hg

theorem uh_one : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  rw [Matrix.conjTranspose_one, one_mul, mul_one]

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) :=
  _root_.WlocSk.UnitaryGroupBasics.uh_mul hg hh

theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) :=
  _root_.WlocSk.UnitaryGroupBasics.uh_inv hg

theorem mem_n_one : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r := (nset_iff 1).2 ⟨uh_one, col_one⟩

theorem mem_n_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) : g * h ∈ Nset k r := by
  have hg' := (nset_iff g).1 hg
  have hh' := (nset_iff h).1 hh
  exact (nset_iff _).2 ⟨uh_mul hg'.1 hh'.1, col_mul hg'.2 hh'.2⟩

theorem mem_n_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g⁻¹ ∈ Nset k r := by
  have hg' := (nset_iff g).1 hg
  have hd := isUnit_of_uh hg'.1
  exact (nset_iff _).2 ⟨uh_inv hg'.1, col_of_left_inv hg'.2 (Matrix.nonsing_inv_mul g hd)⟩

end WeylGroupFacts

open WeylGroupFacts in
theorem unipotent_subgroup_holds : NSubgroup := by
  unfold NSubgroup
  exact fun k r => ⟨WeylGroupFacts.mem_n_one, fun g hg h hh => WeylGroupFacts.mem_n_mul hg hh,
    fun g hg => WeylGroupFacts.mem_n_inv hg⟩

namespace WeylGroupFacts

variable {k r : ℕ}

theorem mul_apply_add {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) (i j : Fin (2 * r + k + 1)) (hir : i.val < r)
    (hj : j.val ≤ r + k) (hij : i.val < j.val) (hji : j.val ≤ i.val + 1 ∨ r ≤ i.val + 1) :
    (g * h) i j = g i j + h i j :=
  _root_.WlocSk.UnitaryGroupBasics.mul_apply_add hg hh i j hir hj hij hji

theorem ell_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : ell k r z (g * h) = ell k r z g + ell k r z h := by
  unfold ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have ha := a.isLt
  by_cases h1 : a.val + 1 < r
  · simp only [dite_eq_left h1]
    exact mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt)
      (by show a.val + 1 ≤ r + k; omega) (by show a.val < a.val + 1; omega)
      (by show a.val + 1 ≤ a.val + 1 ∨ r ≤ a.val + 1; omega)
  · simp only [dite_eq_right h1]
    first
      | simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : q.val < r ∨ r + k < q.val
    · rw [hz q hq]
      simp
    · rw [mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt) (by omega)
        (by show a.val < q.val; omega) (Or.inr (by show r ≤ a.val + 1; omega)), add_mul]

end WeylGroupFacts

open WeylGroupFacts in
theorem length_additive_holds : EllAdd := by
  unfold EllAdd
  intro k r z hz g hg h hh
  exact ell_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2

theorem additive_character_holds : PsiChar := by
  unfold PsiChar
  intro k r z c hz g hg
  refine ⟨fun h hh => ?_, ?_⟩
  · unfold psi
    rw [WeylGroupFacts.ell_mul z hz ((WeylGroupFacts.nset_iff g).1 hg).2 ((WeylGroupFacts.nset_iff h).1 hh).2]
    rw [← Complex.exp_add]
    congr 1
    simp only [mul_add, Complex.add_re, Complex.ofReal_add]
  · unfold psi
    rw [mul_comm Complex.I]
    first
      | exact Complex.norm_exp_ofReal_mul_I _

namespace WeylGroupFacts

variable {k r : ℕ}

theorem col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have hb : ∀ q : Fin (2 * r + k + 1), bvec c q = if q = c then 1 else 0 :=
    fun q => Pi.single_apply c 1 q
  have h1 := congrFun hc p
  first
    | (simp only [Matrix.mulVec, dotProduct, hb, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1; exact h1)

theorem row_of_fixed_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have h1 : hᴴ * Hpk k r * h = Hpk k r := hU
  have h2 := congrFun (congrFun h1 c) j
  have h3 : ∀ q, (hᴴ * Hpk k r) c q = Hpk k r c q := by
    intro q
    rw [Matrix.mul_apply, Fintype.sum_eq_single c]
    · rw [Matrix.conjTranspose_apply, hc c, ite_eq_left rfl, star_one, one_mul]
    · intro p hp
      rw [Matrix.conjTranspose_apply, hc p, ite_eq_right hp, star_zero, zero_mul]
  rw [Matrix.mul_apply] at h2
  simp only [h3] at h2
  rw [Fintype.sum_eq_single (tau k r c)] at h2
  · rw [hpk_row, ite_eq_left rfl, hpk_row] at h2
    have hs : sgn k r c * sgn k r c = 1 := sgn_mul_self c
    calc h (tau k r c) j = (sgn k r c * sgn k r c) * h (tau k r c) j := by rw [hs, one_mul]
      _ = sgn k r c * (sgn k r c * h (tau k r c) j) := by ring
      _ = sgn k r c * (if j = tau k r c then sgn k r c else 0) := by rw [h2]
      _ = if tau k r c = j then 1 else 0 := by
          by_cases hj : j = tau k r c
          · rw [ite_eq_left hj, ite_eq_left hj.symm, hs]
          · rw [ite_eq_right hj, ite_eq_right (Ne.symm hj), mul_zero]
  · intro q hq
    rw [hpk_row, ite_eq_right hq, zero_mul]

theorem tau_out (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (tau k r i).val < r ∨ r + k < (tau k r i).val := by
  have hi' := i.isLt
  simp only [tau, Fin.val_mk]
  split_ifs <;> omega

theorem uw_block {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h :=
  _root_.WlocSk.UnitaryGroupBasics.uw_block hh

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z :=
  _root_.WlocSk.UnitaryGroupBasics.uw_inv hh

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z :=
  _root_.WlocSk.UnitaryGroupBasics.uw_mul hh hh'

theorem block_mul_col {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hg : col k r g) (i q : Fin (2 * r + k + 1)) (hq : q.val ≤ r + k)
    (hi : q.val ≤ i.val ∨ r ≤ i.val) : (h * g) i q = h i q :=
  _root_.WlocSk.UnitaryGroupBasics.block_mul_col hh hg i q hq hi

theorem conj_col {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hinv : h * h' = 1) (hg : col k r g) :
    col k r (h * g * h') :=
  _root_.WlocSk.UnitaryGroupBasics.conj_col hh hh' hinv hg

theorem mul_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  · rw [hrow i, ite_eq_left rfl, one_mul]
  · intro p hp
    rw [hrow p, ite_eq_right (Ne.symm hp), zero_mul]

theorem mul_apply_of_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single j]
  · rw [hcol j, ite_eq_left rfl, mul_one]
  · intro q hq
    rw [hcol q, ite_eq_right hq, mul_zero]

theorem mulVec_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  first
    | simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single i]
  · rw [hrow i, ite_eq_left rfl, one_mul]
  · intro p hp
    rw [hrow p, ite_eq_right (Ne.symm hp), zero_mul]

theorem ell_conj (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    ell k r z (h * g * h') = ell k r z g := by
  unfold block at hh hh'
  unfold ell
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 (eI k r a) p (Or.inl a.isLt)
  by_cases h1 : a.val + 1 < r
  · simp only [dite_eq_left h1]
    rw [mul_assoc, mul_apply_of_row _ _ _ hrow]
    exact mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (Or.inl h1))
  · simp only [dite_eq_right h1]
    rw [mul_assoc, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow, ← Matrix.mulVec_mulVec, hz]

end WeylGroupFacts

open WeylGroupFacts in
theorem unitary_weyl_normal_holds : UWNormal := by
  unfold UWNormal
  intro k r z hz h hh g hg
  have hg' := (nset_iff g).1 hg
  have hinv := uw_inv hh
  have hb := uw_block hh
  have hb' := uw_block hinv
  have hU : h ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hh
    exact hh.1
  have hUi : h⁻¹ ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hinv
    exact hinv.1
  have hzi : h⁻¹ *ᵥ z = z := by
    simp only [UWset, Set.mem_setOf_eq] at hinv
    exact hinv.2.2
  have hd := isUnit_of_uh hU
  exact ⟨(nset_iff _).2 ⟨uh_mul (uh_mul hU hg'.1) hUi,
    conj_col hb hb' (Matrix.mul_nonsing_inv h hd) hg'.2⟩, ell_conj z hb hb' hzi⟩

open WeylGroupFacts in
theorem symmetric_group_holds : SGroup := by
  unfold SGroup
  intro k r z hz
  have hN := unipotent_subgroup_holds k r
  have hW := unitary_weyl_normal_holds k r z hz
  have hW1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
    simp only [UWset, Set.mem_setOf_eq]
    exact ⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨⟨1, hW1, 1, hN.1, (mul_one 1).symm⟩, ?_, ?_⟩
  · rintro s ⟨h, hh, m, hm, rfl⟩ t ⟨h', hh', m', hm', rfl⟩
    have hU' : h' ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh'
      exact hh'.1
    have hd' := isUnit_of_uh hU'
    have hc := (hW h'⁻¹ (uw_inv hh') m hm).1
    rw [Matrix.nonsing_inv_nonsing_inv h' hd'] at hc
    refine ⟨h * h', uw_mul hh hh', h'⁻¹ * m * h' * m', hN.2.1 _ hc _ hm', ?_⟩
    calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
          rw [Matrix.mul_nonsing_inv h' hd', mul_one]
          simp only [mul_assoc]
      _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [mul_assoc]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hd := isUnit_of_uh hU
    have hc := (hW h hh m⁻¹ (hN.2.2 m hm)).1
    refine ⟨h⁻¹, uw_inv hh, h * m⁻¹ * h⁻¹, hc, ?_⟩
    rw [Matrix.mul_inv_rev]
    calc m⁻¹ * h⁻¹ = h⁻¹ * h * m⁻¹ * h⁻¹ := by rw [Matrix.nonsing_inv_mul h hd, one_mul]
      _ = h⁻¹ * (h * m⁻¹ * h⁻¹) := by simp only [mul_assoc]

end Formalism.QuantumDeterminants
