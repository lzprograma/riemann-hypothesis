module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqConjTranspose
import Mathlib.Tactic.Linter.Style
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

private theorem inK_toBlocks₂_eq {k : M2 n} (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  have h3 : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [mul_eq_one_comm.mp hk.2, Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hk.1]
  rw [← fromBlocks_toBlocks k, JJ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h3
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one,
    zero_add, add_zero] at h3
  exact ⟨h3.1, h3.2.1⟩

private theorem inK_toBlocks₁_unitary_relations {k : M2 n} (hk : InK k) :
    (k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂ = 1 ∧
      (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂ = (k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  have hU : kᴴ * k = 1 := hk.2
  rw [← fromBlocks_toBlocks k, hc, hd, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at hU
  simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] at hU
  exact ⟨hU.1, sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hU.2.1)⟩

theorem first_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u1 (g * k) = u1 g * u1 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u1, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₁_mul, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₂_mul, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem second_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u2 (g * k) = u2 g * u2 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u2, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₁_mul, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₂_mul, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem first_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u1 k)ᴴ * u1 k = 1 := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  obtain ⟨h1, h2⟩ := inK_toBlocks₁_unitary_relations hk
  have e : (u1 k)ᴴ * u1 k = ((k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂) +
      Complex.I • ((k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ - (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂) := by
    simp only [u1, hc, hd, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg,
      Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_neg, smul_add, smul_neg, smul_smul, neg_smul, Complex.I_mul_I, neg_mul]
    module
  rw [e, h1, h2, sub_self, smul_zero, add_zero]

def eps (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

theorem eps_sq : eps n * eps n = 1 := by
  simp [eps, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem eps_JJ : eps n * JJ n * eps n = -JJ n := by
  simp [eps, JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

theorem eps_conj : (eps n)ᴴ = eps n := by simp [eps, fromBlocks_conjTranspose]

theorem inK_eps {k : M2 n} (hk : InK k) : InK (eps n * k * eps n) := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have hU : kᴴ * k = 1 := hk.2
  have e : eps n * JJ n * eps n = -JJ n := eps_JJ
  refine ⟨?_, ?_⟩
  · show (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n) = JJ n
    calc (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * JJ n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = -(eps n * (kᴴ * JJ n * k) * eps n) := by
          rw [e]
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hG, e, neg_neg]
  · show (eps n * k * eps n)ᴴ * (eps n * k * eps n) = 1
    calc (eps n * k * eps n)ᴴ * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [eps_sq, Matrix.mul_one, hU, Matrix.mul_one, eps_sq]

theorem first_cayley_block_swap_conj (k : M2 n) : u1 (eps n * k * eps n) = u2 k := by
  simp [u1, u2, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₁_mul, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₂_mul, eps]

theorem second_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u2 k)ᴴ * u2 k = 1 := by
  rw [← first_cayley_block_swap_conj]
  exact first_cayley_block_compact_unitary (inK_eps hk)

theorem second_cayley_block_inv_eq_conjTranspose {k : M2 n} (hk : InK k) : (u2 k)⁻¹ = (u2 k)ᴴ := Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk)

theorem inverse_second_block_eq_neg_conjTranspose {x : M2 n} (hx : InG x) : ub2 x = -(u2 x)ᴴ := by
  rw [ub2, inv_of_inG hx, u2]
  conv_lhs => rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁]
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]

theorem Om_K {k : M2 n} (hk : InK k) : Om k = -((u2 k)⁻¹ * u1 k) := by
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose hk.1, inverse_first_block_eq_conjTranspose hk.1, Matrix.inv_eq_left_inv (mul_eq_one_comm.mp (first_cayley_block_compact_unitary hk)),
    ← second_cayley_block_inv_eq_conjTranspose hk, Matrix.neg_mul]

theorem normSq_det_u1K {k : M2 n} (hk : InK k) : Complex.normSq (u1 k).det = 1 := by
  have h := congrArg Matrix.det (first_cayley_block_compact_unitary hk)
  rw [det_mul, det_conjTranspose, det_one] at h
  have h' : (Complex.normSq (u1 k).det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast h'

theorem fz_K (m : ℕ) (e : ℤ) (z : ℂ) {k : M2 n} (hk : InK k) : fz m e z k = fz m e 0 k := by
  have hd : (u1 k).det * (ub1 k).det = 1 := by
    rw [inverse_first_block_eq_conjTranspose hk.1, Matrix.det_conjTranspose, Complex.star_def, mul_comm,
      ← Complex.normSq_eq_conj_mul_self, normSq_det_u1K hk, Complex.ofReal_one]
  simp only [fz, hd, Complex.one_cpow, neg_zero, Complex.cpow_zero]

theorem first_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u1 (p * y) = p.toBlocks₂₂ * u1 y := by
  simp only [u1, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₁_mul, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₂_mul, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]

theorem second_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u2 (p * y) = p.toBlocks₂₂ * u2 y := by
  simp only [u2, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₁_mul, _root_.PositivityTheory.Rg.Sw.LVs.toBlocks₂₂_mul, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_neg]

theorem Om_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) : Om (p * y) = Om y := by
  have hp' : pᴴ * JJ n * p = JJ n := hp
  rw [← fromBlocks_toBlocks p, hp21, JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at hp'
  have hq : (p.toBlocks₂₂)ᴴ * p.toBlocks₁₁ = 1 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hp'.2.1
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose (_root_.PositivityTheory.Rg.Sw.LVs.inG_mul hp hy), inverse_first_block_eq_conjTranspose (_root_.PositivityTheory.Rg.Sw.LVs.inG_mul hp hy), inverse_second_block_eq_neg_conjTranspose hy, inverse_first_block_eq_conjTranspose hy, second_cayley_block_upper_triangular_mul hp21, first_cayley_block_upper_triangular_mul hp21,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hq,
    Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (p.toBlocks₂₂)ᴴ, hq, Matrix.one_mul]

def lam (m : ℕ) (e : ℤ) (z : ℂ) (p : M2 n) : ℂ :=
  p.det ^ e * (p.toBlocks₂₂).det ^ (-(m : ℤ)) * ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) ^ (-z)

theorem fz_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (m : ℕ) (e : ℤ) (z : ℂ) :
    fz m e z (p * y) = lam m e z p * fz m e z y := by
  have h1 : (u1 (p * y)).det = (p.toBlocks₂₂).det * (u1 y).det := by rw [first_cayley_block_upper_triangular_mul hp21, Matrix.det_mul]
  have h2 : (u1 (p * y)).det * (ub1 (p * y)).det =
      ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) * ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose (_root_.PositivityTheory.Rg.Sw.LVs.inG_mul hp hy), Matrix.det_conjTranspose, h1, star_mul', Complex.star_def,
      Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have h3 : (u1 y).det * (ub1 y).det = ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hy, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  simp only [fz, lam]
  rw [h2, h3, h1, Matrix.det_mul, mul_zpow, mul_zpow,
    Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]
  ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
