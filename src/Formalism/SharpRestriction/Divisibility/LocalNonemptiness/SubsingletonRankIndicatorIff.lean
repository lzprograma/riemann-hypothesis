module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.Order.Star.Int

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.MainNotions.ModuliIntegralCharts NumberField

namespace LocalProvisionModel

section Form

variable (D : D7)

def cjO : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem cjO_coe (c : 𝓞 D.host.E) : ((cjO D c : 𝓞 D.host.E) : D.host.E) = D.host.conj (c : D.host.E) := rfl

theorem emb_conj (σ : D.host.E →ₐ[ℚ] ℂ) (x : D.host.E) : σ (D.host.conj x) = starRingEnd ℂ (σ x) := by
  exact (D.host.der.conj_iff (σ : D.host.E →+* ℂ) D.host.conj).mpr
    (D.host.gal.apply_symm_apply _) x

def beO : 𝓞 D.host.E →ₗ[ℤ] 𝓞 D.host.E →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun a b => ((Algebra.trace ℤ (𝓞 D.host.E) (a * cjO D b) : ℤ) : ℝ))
    (by intro a a' b; rw [add_mul, map_add (f := _), Int.cast_add])
    (by intro c a b; rw [smul_mul_assoc, map_smul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul])
    (by intro a b b'; rw [map_add (f := _), mul_add, map_add (f := _), Int.cast_add])
    (by intro c a b; rw [map_zsmul, mul_smul_comm, map_smul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul])

theorem beO_apply (a b : 𝓞 D.host.E) :
    beO D a b = ((Algebra.trace ℤ (𝓞 D.host.E) (a * cjO D b) : ℤ) : ℝ) := rfl

theorem trC (x : 𝓞 D.host.E) :
    ((Algebra.trace ℤ (𝓞 D.host.E) x : ℤ) : ℂ) = ∑ σ : D.host.E →ₐ[ℚ] ℂ, σ (x : D.host.E) := by
  have h1 := Algebra.coe_trace_int x
  have h2 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := D.host.E) (x := (x : D.host.E))
  rw [← h2, ← h1]
  simp

theorem beO_eq (a b : 𝓞 D.host.E) : ((beO D a b : ℝ) : ℂ) =
    ∑ σ : D.host.E →ₐ[ℚ] ℂ, σ (a : D.host.E) * starRingEnd ℂ (σ (b : D.host.E)) := by
  rw [beO_apply, Complex.ofReal_intCast, trC]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have e : ((a * cjO D b : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * D.host.conj (b : D.host.E) := by
    rw [← cjO_coe]; norm_cast
  rw [e, map_mul, emb_conj]

theorem beO_symm (a b : 𝓞 D.host.E) : beO D a b = beO D b a := by
  apply Complex.ofReal_injective

  rw [← Complex.conj_ofReal (beO D a b : ℝ), beO_eq, beO_eq, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem beO_bal (c c' : 𝓞 D.host.E) (h : (c' : D.host.E) = D.host.conj (c : D.host.E)) (a b : 𝓞 D.host.E) :
    beO D (c • a) b = beO D a (c' • b) := by
  apply Complex.ofReal_injective
  rw [beO_eq, beO_eq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : σ (c' : D.host.E) = starRingEnd ℂ (σ (c : D.host.E)) := by rw [h, emb_conj]
  have e1 : ((c • a : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * a := by
    rw [smul_eq_mul]; norm_cast
  have e2 : ((c' • b : 𝓞 D.host.E) : D.host.E) = (c' : D.host.E) * b := by
    rw [smul_eq_mul]; norm_cast
  rw [e1, e2, map_mul, map_mul, map_mul, hc, Complex.conj_conj]
  ring

def beK (k : ℕ) : (Fin k → 𝓞 D.host.E) →ₗ[ℤ] (Fin k → 𝓞 D.host.E) →ₗ[ℤ] ℝ :=
  ∑ i, (beO D).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem beK_apply (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : beK D k a b = ∑ i, beO D (a i) (b i) := by
  simp [beK, LinearMap.sum_apply, LinearMap.compl₁₂_apply]

theorem beO_sum {ι : Type} [Fintype ι] (a : ι → 𝓞 D.host.E) (c : ι → ℝ) :
    ∑ i, ∑ j, c i * c j * beO D (a i) (a j) =
      ∑ σ : D.host.E →ₐ[ℚ] ℂ, Complex.normSq (∑ i, (c i : ℂ) * σ (a i : D.host.E)) := by
  apply Complex.ofReal_injective
  calc ((∑ i, ∑ j, c i * c j * beO D (a i) (a j) : ℝ) : ℂ)
      = ∑ i, ∑ j, ∑ σ : D.host.E →ₐ[ℚ] ℂ,
          (c i : ℂ) * c j * (σ (a i : D.host.E) * starRingEnd ℂ (σ (a j : D.host.E))) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [beO_eq, Finset.mul_sum]
    _ = ∑ i, ∑ σ : D.host.E →ₐ[ℚ] ℂ, ∑ j,
          (c i : ℂ) * c j * (σ (a i : D.host.E) * starRingEnd ℂ (σ (a j : D.host.E))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ σ : D.host.E →ₐ[ℚ] ℂ, ∑ i, ∑ j,
          (c i : ℂ) * c j * (σ (a i : D.host.E) * starRingEnd ℂ (σ (a j : D.host.E))) :=
        Finset.sum_comm
    _ = ((∑ σ : D.host.E →ₐ[ℚ] ℂ, Complex.normSq (∑ i, (c i : ℂ) * σ (a i : D.host.E)) : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun σ _ => ?_

        rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, Complex.conj_ofReal]
        ring

theorem beK_sum (k : ℕ) {ι : Type} [Fintype ι] (a : ι → Fin k → 𝓞 D.host.E) (c : ι → ℝ) :
    ∑ i, ∑ j, c i * c j * beK D k (a i) (a j) =
      ∑ m : Fin k, ∑ σ : D.host.E →ₐ[ℚ] ℂ, Complex.normSq (∑ i, (c i : ℂ) * σ (a i m : D.host.E)) := by
  simp only [beK_apply, Finset.mul_sum]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact beO_sum D (fun i => a i m) c

def bK (k : ℕ) : Module.Basis (Σ _ : Fin k, Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) ℤ (Fin k → 𝓞 D.host.E) :=
  Pi.basis fun _ => RingOfIntegers.basis D.host.E

theorem beK_posDef (k : ℕ) (c : (Σ _ : Fin k, Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * beK D k (bK D k i) (bK D k j) := by
  obtain ⟨⟨m0, t0⟩, h0⟩ := Function.ne_iff.mp hc
  have key : ∃ σ : D.host.E →ₐ[ℚ] ℂ,
      ∑ i, (c i : ℂ) * σ ((bK D k i m0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    by_contra! hne
    let B := NumberField.integralBasis D.host.E
    have hred : ∀ σ : D.host.E →ₐ[ℚ] ℂ, ∑ t, (c ⟨m0, t⟩ : ℂ) * σ (B t) = 0 := by
      intro σ
      have h := hne σ
      rw [Fintype.sum_sigma, Finset.sum_eq_single m0 (fun m' _ hm' => ?_) (by simp)] at h
      · rw [← h]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp [B, bK, Pi.basis_apply, NumberField.integralBasis_apply]
      · refine Finset.sum_eq_zero fun t _ => ?_
        simp [bK, Pi.basis_apply, Ne.symm hm']
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) =
        Fintype.card (D.host.E →ₐ[ℚ] ℂ) := by
      rw [AlgHom.card, Module.finrank_eq_card_basis B]
    let e := Fintype.equivOfCardEq hcard
    have hdet : (Algebra.embeddingsMatrixReindex ℚ ℂ B e).det ≠ 0 := by
      intro hd
      have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ B e
      rw [hd, zero_pow two_ne_zero, map_eq_zero_iff _ (algebraMap ℚ ℂ).injective] at h2
      exact Algebra.discr_not_zero_of_basis ℚ B h2
    have hv := Matrix.eq_zero_of_vecMul_eq_zero hdet (v := fun t => (c ⟨m0, t⟩ : ℂ)) (by
      funext j
      simp only [Matrix.vecMul, dotProduct, Algebra.embeddingsMatrixReindex,
        Algebra.embeddingsMatrix, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.of_apply, Pi.zero_apply]
      exact hred (e j))
    have h1 := congrFun hv t0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h1
    exact h0 h1
  obtain ⟨σ, hσ⟩ := key
  rw [beK_sum]
  refine Finset.sum_pos' (fun m _ => Finset.sum_nonneg fun σ _ => Complex.normSq_nonneg _)
    ⟨m0, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
    ⟨σ, Finset.mem_univ _, Complex.normSq_pos.mpr hσ⟩


open Classical in
def rk01 (P : Prop) : ℕ := if P then 0 else 1

theorem rank_indicator_le_one (P : Prop) : rk01 P ≤ 1 := by
  unfold rk01
  split_ifs <;> omega

theorem finrank_copies (k : ℕ) : Module.finrank ℤ (Fin k → 𝓞 D.host.E) = 2 * D.R.f * k := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, NumberField.RingOfIntegers.rank, D.host.der.finrank_E]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring


def pmM (dg : PsiT D → ℕ → ℤ) (n : ℕ) : ℤ := ∑ t : D.what₂.Tau, ∑ k ∈ Finset.Icc 1 n, |dg (D.eTau t) k|

theorem pmM_nonneg (dg : PsiT D → ℕ → ℤ) (n : ℕ) : 0 ≤ pmM D dg n := by
  exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun k _ => abs_nonneg _

theorem abs_le_pmM (dg : PsiT D → ℕ → ℤ) (n : ℕ) (τ : PsiT D) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 n) :
    |∑ k ∈ s, dg τ k| ≤ pmM D dg n := by
  have h1 : |∑ k ∈ s, dg τ k| ≤ ∑ k ∈ s, |dg τ k| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ k ∈ s, |dg τ k| ≤ ∑ k ∈ Finset.Icc 1 n, |dg τ k| :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => abs_nonneg _)
  have h3 : ∑ k ∈ Finset.Icc 1 n, |dg τ k| ≤ pmM D dg n := by
    unfold pmM
    have := Finset.single_le_sum (f := fun t => ∑ k ∈ Finset.Icc 1 n, |dg (D.eTau t) k|)
      (fun t _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ (D.eTau.symm τ))
    simpa using this
  linarith

end Form

def nn (n : ℕ) : ℕ := if n = 0 then 1 else n

instance (n : ℕ) : NeZero (nn n) := ⟨by unfold nn; split_ifs <;> omega⟩

abbrev AtM (k n : ℕ) : Type := Fin k → ZMod (nn n)

theorem atM_tors (k n : ℕ) (x : AtM k n) : n • x = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  by_cases h : n = 0
  · simp [h]
  · have hn : nn n = n := ite_eq_right h
    have : (n : ZMod (nn n)) = 0 := (CharP.cast_eq_zero_iff (ZMod (nn n)) (nn n) n).mpr (by rw [hn])
    rw [this, zero_mul]

theorem atM_card (k n : ℕ) (h : 0 < n) : Fintype.card (AtM k n) = n ^ k := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, (show nn n = n from ite_eq_right (by omega))]

structure MP (D : D7) (p : ℕ) where
  K : CF p
  Gn : Type
  fin : Finite Gn
  ne : Nonempty Gn
  ab : Gn → Prop
  Cv : Type
  dg : Cv → PsiT D → ℕ → ℤ

def mpTrivialAb (D : D7) (p : ℕ) (K : CF p) : MP D p where
  K := K
  Gn := Unit
  fin := inferInstance
  ne := ⟨()⟩
  ab := fun _ => True
  Cv := Empty
  dg := fun c => c.elim

end LocalProvisionModel

open LocalProvisionModel

variable (D : D7)

end Formalism.MainNotions.DIV.Inh

end
