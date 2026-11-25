module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitude
import GroundTheory.Brauer.TensorSimple
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MarkEll

theorem star_mulVec_dot {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    star (M *ᵥ a) ⬝ᵥ (A *ᵥ (M *ᵥ b)) = star a ⬝ᵥ ((Mᴴ * A * M) *ᵥ b) := by
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

theorem normSq_eq_of_form {n : ℕ} (Γ A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hΓ : Γᴴ * A * Γ = (c : ℂ) • A)
    (x : Fin n → ℂ) (w : ℂ) (hx : Γ *ᵥ x = w • x) (h0 : star x ⬝ᵥ (A *ᵥ x) ≠ 0) : ‖w‖ ^ 2 = c := by
  have h := star_mulVec_dot Γ A x x
  rw [hΓ, hx] at h
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  rw [← mul_assoc] at h
  have h2 : w * star w = (c : ℂ) := mul_right_cancel₀ h0 h
  have h3 : ((‖w‖ ^ 2 : ℝ) : ℂ) = (c : ℂ) := by
    rw [← h2, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h3

theorem natDegree_minpoly_le_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra! hlt
  have hsum := Polynomial.aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [Polynomial.coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem eigA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : G.C) (v : InfinitePlace G.F) (z : ℂ),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).eval₂ v.embedding z = 0 →
    ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v g *ᵥ x = z • x := by
  intros
  apply _root_.GlobalTheory.LKCx.PolyArch.roots_eig_any <;> assumption

theorem normSq_of_eigenvector {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ) (ha : G.a = 1)
    (hm : P.Mark μ) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) (hx0 : x ≠ 0) (w : ℂ)
    (hx : G.psi v P.γ *ᵥ x = w • x) : ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  obtain ⟨-, -, hΓ⟩ := GlobalTheory.LKMid.pair_form_laws p G P v
  obtain ⟨Z, hZ⟩ := GlobalTheory.LKMid.Pair.gram_psi_inv_congr p G P v
  set A := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hAdef
  set Γ := G.psi v P.γ with hΓdef
  have hΓ' : Γᴴ * A * Γ = ((((P.c : ℚ) : ℝ)) : ℂ) • A := by rw [hΓ]; push_cast; rfl
  have cong : ∀ a b : Fin G.n → ℂ, star a ⬝ᵥ (A *ᵥ b) =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a) ⬝ᵥ (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b)) := by
    intro a b; rw [star_mulVec_dot, ← hZ]
  have Zne : ∀ a : Fin G.n → ℂ, a ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a ≠ 0 := by
    intro a ha h
    apply ha
    have := congrArg (fun y => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) h
    simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero] using this
  have hc0 : ((((P.c : ℚ) : ℝ)) : ℂ) ≠ 0 := by
    have : ((P.c : ℚ)) ≠ 0 := P.c.ne_zero
    exact_mod_cast this
  rcases G.sig v with ⟨h1, -⟩ | ⟨h0, -⟩
  · obtain ⟨v0, hv0, x0, hx0e, hpos⟩ := hm
    have hv : v = v0 := by
      have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := by
        have := ha; unfold HTGroup.a at this; omega
      haveI := Fintype.card_le_one_iff_subsingleton.mp hcard
      exact congrArg Subtype.val (Subsingleton.elim (⟨v, h1⟩ : {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1})
        ⟨v0, hv0⟩)
    subst hv
    have hS0 : star x0 ⬝ᵥ (A *ᵥ x0) ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hμ : ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := normSq_eq_of_form Γ A _ hΓ' x0 μ hx0e hS0
    by_cases hw : w = μ
    · rw [hw]; exact hμ
    · have hS : star x0 ⬝ᵥ (A *ᵥ x) = 0 := by
        by_contra hne
        have h := star_mulVec_dot Γ A x0 x
        rw [hΓ', hx0e, hx] at h
        simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
          smul_eq_mul] at h
        rw [← mul_assoc] at h
        have h2 := mul_right_cancel₀ hne h
        have hμ2 : μ * star μ = ((((P.c : ℚ) : ℝ)) : ℂ) := by
          rw [← hμ, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hμ0 : star μ ≠ 0 := by
          intro h0; apply hc0; rw [← hμ2, h0, mul_zero]
        apply hw
        apply mul_right_cancel₀ hμ0
        rw [hμ2]
        first | exact h2
      apply normSq_eq_of_form Γ A _ hΓ' x w hx
      intro h
      have hneg := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _
        (by rw [← cong]; exact hpos) (by rw [← cong]; exact hS) (Zne x hx0)
      rw [← cong, h] at hneg; simp at hneg
  · apply normSq_eq_of_form Γ A _ hΓ' x w hx
    intro h
    have hneg := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (Zne x hx0)
    rw [← cong, h] at hneg; simp at hneg

theorem mark_ell : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ ha hm φ z hz
  have hdeg : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) z hdeg (by rw [h]; exact hz)
    exact normSq_of_eigenvector G P μ ha hm _ x hx0 z hx
  · have hz' : (minpoly G.F (P.γ : G.C)).eval₂ (InfinitePlace.mk φ).embedding (star z) = 0 := by
      have e : (InfinitePlace.mk φ).embedding = (starRingEnd ℂ).comp φ := by
        rw [h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := Polynomial.hom_eval₂ P.pol φ (starRingEnd ℂ) z
      rw [hz, map_zero] at this
      rw [e]; exact this.symm
    obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) (star z) hdeg hz'
    have := normSq_of_eigenvector G P μ ha hm _ x hx0 (star z) hx
    rwa [norm_star] at this

end GlobalTheory.LKMid.MarkEll
