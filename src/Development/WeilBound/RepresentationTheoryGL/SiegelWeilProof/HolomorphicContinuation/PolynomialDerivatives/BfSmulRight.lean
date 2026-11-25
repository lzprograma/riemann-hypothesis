module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC.CoreC.G

variable {τ : Type} [Fintype τ] [DecidableEq τ]

def gf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, star (p.coeff s) * q.coeff s * w s

variable (w : (τ →₀ ℕ) → ℂ)

theorem gf_eq (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S) (hq : q.support ⊆ S) :
    gf w p q = ∑ s ∈ S, star (p.coeff s) * q.coeff s * w s := by
  unfold gf
  refine Finset.sum_subset (Finset.union_subset hp hq) fun s _ hs => ?_
  simp only [Finset.mem_union, not_or] at hs
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs.1 (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem gf_add_left (p p' q : MvPolynomial τ ℂ) : gf w (p + p') q = gf w p q + gf w p' q := by
  classical
  have h1 := support_add (p := p) (q := p')
  rw [gf_eq w (p.support ∪ p'.support ∪ q.support) (h1.trans Finset.subset_union_left) Finset.subset_union_right,
    gf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_left).trans Finset.subset_union_left)
      Finset.subset_union_right,
    gf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_right).trans Finset.subset_union_left)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [star_add]; ring

theorem gf_add_right (p q q' : MvPolynomial τ ℂ) : gf w p (q + q') = gf w p q + gf w p q' := by
  classical
  have h1 := support_add (p := q) (q := q')
  rw [gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left (h1.trans Finset.subset_union_right),
    gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_left).trans Finset.subset_union_right),
    gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_right).trans Finset.subset_union_right), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp; ring

theorem gf_smul_left (r : ℂ) (p q : MvPolynomial τ ℂ) : gf w (r • p) q = star r * gf w p q := by
  classical
  rw [gf_eq w (p.support ∪ q.support) ((MvPolynomial.support_smul).trans Finset.subset_union_left) Finset.subset_union_right,
    gf_eq w (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [star_mul]; ring

theorem gf_smul_right (r : ℂ) (p q : MvPolynomial τ ℂ) : gf w p (r • q) = r * gf w p q := by
  classical
  rw [gf_eq w (p.support ∪ q.support) Finset.subset_union_left ((MvPolynomial.support_smul).trans Finset.subset_union_right),
    gf_eq w (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp; ring

theorem gf_neg_left (p q : MvPolynomial τ ℂ) : gf w (-p) q = -gf w p q := by
  rw [show -p = (-1 : ℂ) • p by simp, gf_smul_left]; simp

theorem gf_neg_right (p q : MvPolynomial τ ℂ) : gf w p (-q) = -gf w p q := by
  rw [show -q = (-1 : ℂ) • q by simp, gf_smul_right]; simp

theorem gf_sub_left (p p' q : MvPolynomial τ ℂ) : gf w (p - p') q = gf w p q - gf w p' q := by
  rw [sub_eq_add_neg, gf_add_left, gf_neg_left, ← sub_eq_add_neg]

theorem gf_sub_right (p q q' : MvPolynomial τ ℂ) : gf w p (q - q') = gf w p q - gf w p q' := by
  rw [sub_eq_add_neg, gf_add_right, gf_neg_right, ← sub_eq_add_neg]

theorem gf_sum_left {ι : Type} (I : Finset ι) (f : ι → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ) :
    gf w (∑ i ∈ I, f i) q = ∑ i ∈ I, gf w (f i) q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [gf]
  | insert a I ha ih => rw [Finset.sum_insert ha, gf_add_left, ih, Finset.sum_insert ha]

theorem gf_sum_right {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    gf w p (∑ i ∈ I, f i) = ∑ i ∈ I, gf w p (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [gf]
  | insert a I ha ih => rw [Finset.sum_insert ha, gf_add_right, ih, Finset.sum_insert ha]

theorem gf_monomial (s t : τ →₀ ℕ) (a b : ℂ) :
    gf w (monomial s a) (monomial t b) = if s = t then star a * b * w s else 0 := by
  classical
  rw [gf_eq w {s, t} ((support_monomial_subset).trans (by simp)) ((support_monomial_subset).trans (by simp))]
  by_cases h : s = t
  · subst h; simp [coeff_monomial]
  · rw [Finset.sum_pair h]; simp [coeff_monomial, h, Ne.symm h]

theorem gf_induction {P : MvPolynomial τ ℂ → MvPolynomial τ ℂ → Prop}
    (hm : ∀ s t (a b : ℂ), P (monomial s a) (monomial t b))
    (hl : ∀ p p' q, P p q → P p' q → P (p + p') q) (hr : ∀ p q q', P p q → P p q' → P p (q + q')) :
    ∀ p q, P p q := by
  intro p q
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    induction q using MvPolynomial.induction_on' with
    | monomial t b => exact hm s t a b
    | add q q' h1 h2 => exact hr _ _ _ h1 h2
  | add p p' h1 h2 => exact hl _ _ _ h1 h2

variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw

theorem gf_X_mul (k : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * p) q = κ * gf w p (pderiv k q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, gf_monomial, gf_monomial]
    by_cases h : Finsupp.single k 1 + s = t
    · subst h
      rw [ite_eq_left rfl, ite_eq_left (add_tsub_cancel_left _ _).symm, hw]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [ite_eq_right h]
      by_cases h' : s = t - Finsupp.single k 1
      · rw [ite_eq_left h']
        have : t k = 0 := by
          by_contra h0
          apply h
          rw [h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [ite_eq_right h']; ring
  · rw [mul_add, gf_add_left, gf_add_left, h1, h2, mul_add]
  · rw [gf_add_right, map_add (f := _), gf_add_right, h1, h2, mul_add]

theorem gf_pderiv (k : τ) (p q : MvPolynomial τ ℂ) : κ * gf w (pderiv k p) q = gf w p (X k * q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, gf_monomial, gf_monomial]
    by_cases h : s = Finsupp.single k 1 + t
    · subst h
      rw [ite_eq_left rfl, ite_eq_left (add_tsub_cancel_left _ _), hw, add_tsub_cancel_left]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, star_mul]
      push_cast
      simp only [Complex.star_def, Complex.conj_natCast, map_add (f := _), map_one]
      ring
    · rw [ite_eq_right h]
      by_cases h' : s - Finsupp.single k 1 = t
      · rw [ite_eq_left h']
        have : s k = 0 := by
          by_contra h0
          apply h
          rw [← h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [ite_eq_right h']; ring
  · rw [map_add (f := _), gf_add_left, gf_add_left, ← h1, ← h2, mul_add]
  · rw [gf_add_right, mul_add, mul_add, gf_add_right, h1, h2]

theorem gf_adj (k l : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * pderiv l p) q = gf w p (X l * pderiv k q) := by
  rw [gf_X_mul κ hw, gf_pderiv κ hw]

omit hw

variable (w) in
theorem gf_herm (hs : ∀ s, star (w s) = w s) (p q : MvPolynomial τ ℂ) : gf w q p = star (gf w p q) := by
  unfold gf
  rw [Finset.union_comm, star_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [star_mul, star_mul, star_star, hs]; ring

variable (w) in
theorem gf_pos (hs : ∀ s, star (w s) = w s) (hp : ∀ s, 0 < (w s).re) (p : MvPolynomial τ ℂ) (h : p ≠ 0) :
    0 < (gf w p p).re := by
  unfold gf
  rw [Finset.union_self, Complex.re_sum]
  obtain ⟨s, hs0⟩ := (MvPolynomial.ne_zero_iff).mp h
  have hmem : s ∈ p.support := MvPolynomial.mem_support_iff.mpr hs0
  have key : ∀ t, (star (p.coeff t) * p.coeff t * w t).re = Complex.normSq (p.coeff t) * (w t).re := by
    intro t
    have hw' : (w t).im = 0 := by
      have := congrArg Complex.im (hs t); simp at this; linarith
    rw [show star (p.coeff t) * p.coeff t = (Complex.normSq (p.coeff t) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]; rfl]
    simp [Complex.mul_re, hw']
  refine Finset.sum_pos' (fun t _ => ?_) ⟨s, hmem, ?_⟩
  · rw [key]; exact mul_nonneg (Complex.normSq_nonneg _) (hp t).le
  · rw [key]; exact mul_pos (Complex.normSq_pos.mpr hs0) (hp s)

theorem der_expand (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, D (X v) * pderiv v p := by
  let D' : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ) := ∑ v, D (X v) • pderiv (R := ℂ) v
  have hD' : ∀ q, D' q = ∑ v, D (X v) * pderiv v q := fun q => by
    change (D' : MvPolynomial τ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) q = _
    simp [D', Derivation.coe_sum_linearMap, LinearMap.sum_apply, Derivation.coe_smul_linearMap,
      smul_eq_mul]
  have h : D = D' := MvPolynomial.derivation_ext fun u => by
    simp [hD', Pi.single_apply, mul_ite]
  exact (DFunLike.congr_fun h p).trans (hD' p)

theorem der_expand2 (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, ∑ u, (D (X v)).coeff (Finsupp.single u 1) • (X u * pderiv v p) := by
  rw [der_expand D p]
  refine Finset.sum_congr rfl fun v _ => ?_
  conv_lhs => rw [hlin v]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_mul_assoc]

theorem der_adj {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (D D' : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u)
    (hlin' : ∀ v, D' (X v) = ∑ u, (D' (X v)).coeff (Finsupp.single u 1) • X u)
    (htr : ∀ v u, (D' (X u)).coeff (Finsupp.single v 1) = star ((D (X v)).coeff (Finsupp.single u 1)))
    (p q : MvPolynomial τ ℂ) : gf w (D p) q = gf w p (D' q) := by
  rw [der_expand2 D hlin p, der_expand2 D' hlin' q]
  simp_rw [gf_sum_left, gf_sum_right, gf_smul_left, gf_smul_right, gf_adj κ hw, htr]
  rw [Finset.sum_comm]

def bf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, p.coeff s * q.coeff s * w s

private theorem bf_eq_gf {τ : Type} [DecidableEq τ] (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) :
    bf w p q = gf w (map (starRingEnd ℂ) p) q := by
  have hs : (map (starRingEnd ℂ) p).support = p.support :=
    Finset.ext fun s => by simp [MvPolynomial.mem_support_iff, coeff_map]
  simp only [bf, gf, hs, coeff_map, ← Complex.star_def, star_star]

theorem bf_eq (w : (τ →₀ ℕ) → ℂ) (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S)
    (hq : q.support ⊆ S) : bf w p q = ∑ s ∈ S, p.coeff s * q.coeff s * w s := by
  rw [bf_eq_gf, gf_eq w S ((support_map_subset (starRingEnd ℂ) p).trans hp) hq]
  simp only [coeff_map, ← Complex.star_def, star_star]

theorem bf_monomial (w : (τ →₀ ℕ) → ℂ) (s t : τ →₀ ℕ) (a b : ℂ) :
    bf w (monomial s a) (monomial t b) = if s = t then a * b * w s else 0 := by
  rw [bf_eq_gf, map_monomial, gf_monomial, ← Complex.star_def, star_star]

theorem bf_X_mul {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (k : τ) (p q : MvPolynomial τ ℂ) : bf w (X k * p) q = κ * bf w p (pderiv k q) := by
  rw [bf_eq_gf, map_mul, map_X, gf_X_mul κ hw, ← bf_eq_gf]

theorem bf_pderiv {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (k : τ) (p q : MvPolynomial τ ℂ) : κ * bf w (pderiv k p) q = bf w p (X k * q) := by
  rw [bf_eq_gf, ← pderiv_map, gf_pderiv κ hw, ← bf_eq_gf]

theorem bf_sum_left (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (f : ι → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ) :
    bf w (∑ i ∈ I, f i) q = ∑ i ∈ I, bf w (f i) q := by
  rw [bf_eq_gf, map_sum, gf_sum_left]
  simp_rw [← bf_eq_gf]

theorem bf_sum_right (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    bf w p (∑ i ∈ I, f i) = ∑ i ∈ I, bf w p (f i) := by
  rw [bf_eq_gf, gf_sum_right]
  simp_rw [← bf_eq_gf]

end PositivityTheory.Rg.Sw.LC.CoreC.G
