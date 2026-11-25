module

public import Formalism.PeriodIntegrals.NormGramAtOrigin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

private lemma hform_eq_toLinearMapₛₗ₂' {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x y = Matrix.toLinearMapₛₗ₂' E σ (RingHom.id E) J x y := by
  rw [PI.NormGramAtOrigin.hform, Matrix.toLinearMapₛₗ₂'_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [RingHom.id_apply, smul_eq_mul]; ring

private lemma hform_symm_of_involutive_of_hermitian {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (PI.NormGramAtOrigin.hform σ J x y) = PI.NormGramAtOrigin.hform σ J y x := by

  simp only [PI.NormGramAtOrigin.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hJ j i]; ring

private lemma hform_add_smul_self_ne_zero_of_isotropic_pair {E : Type} [Field E] [CharZero E]
    (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (w y : Fin n → E)
    (hw : PI.NormGramAtOrigin.hform σ J w w = 0) (hy : PI.NormGramAtOrigin.hform σ J y y = 0)
    (t : E) (ht : PI.NormGramAtOrigin.hform σ J w y = t) (ht0 : t ≠ 0) :
    PI.NormGramAtOrigin.hform σ J (w + σ t • y) (w + σ t • y) ≠ 0 := by
  have hyw : PI.NormGramAtOrigin.hform σ J y w = σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w y, ht]
  rw [hform_eq_toLinearMapₛₗ₂'] at hw hy ht hyw ⊢
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul, hσ, hw, hy, ht, hyw]
  have hs : σ t ≠ 0 := fun h => ht0 (by rw [← hσ t, h, map_zero])
  rw [show 0 + t * σ t + σ t * (t + t * 0) = 2 * (t * σ t) by ring]
  exact mul_ne_zero two_ne_zero (mul_ne_zero ht0 hs)

private lemma exists_hform_ne_zero_of_det_ne_zero {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJd : J.det ≠ 0) (y : Fin n → E) (hy : y ≠ 0) :
    ∃ z : Fin n → E, PI.NormGramAtOrigin.hform σ J z y ≠ 0 := by
  have hJy : Matrix.mulVec J y ≠ 0 := fun h => hJd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy, h⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hJy
  refine ⟨Pi.single i 1, ?_⟩
  have e : PI.NormGramAtOrigin.hform σ J (Pi.single i 1) y = Matrix.mulVec J y i := by
    unfold PI.NormGramAtOrigin.hform
    rw [Finset.sum_eq_single i]
    · simp [Matrix.mulVec, dotProduct]
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e]
  exact hi

private lemma hermC_ppos_col_castLE {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin k → Fin n → E)
    (hvo : ∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0)
    (hvd : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0) (z y0 : Fin n → E)
    (hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0) (hz : PI.NormGramAtOrigin.hform σ J z y0 ≠ 0) :
    ∃ p : Fin n → E, (∀ b, PI.NormGramAtOrigin.hform σ J (v b) p = 0) ∧ PI.NormGramAtOrigin.hform σ J p y0 ≠ 0 := by
  refine ⟨z - ∑ a, (PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a,
    fun b => ?_, ?_⟩
  · rw [hform_eq_toLinearMapₛₗ₂', map_sub, map_sum, Finset.sum_eq_single b]
    · simp only [LinearMap.map_smulₛₗ, RingHom.id_apply, smul_eq_mul, ← hform_eq_toLinearMapₛₗ₂',
        div_mul_cancel₀ _ (hvd b), sub_self]
    · intro a _ hab
      simp only [LinearMap.map_smulₛₗ, RingHom.id_apply, smul_eq_mul, ← hform_eq_toLinearMapₛₗ₂',
        hvo b a (Ne.symm hab), mul_zero]
    · exact fun h => absurd (Finset.mem_univ b) h
  · rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y0, hform_eq_toLinearMapₛₗ₂',
      map_sub, map_sum]
    have h0 : ∀ a, Matrix.toLinearMapₛₗ₂' E σ (RingHom.id E) J y0
        ((PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) •
          v a) = 0 := fun a => by
      rw [LinearMap.map_smulₛₗ, RingHom.id_apply, smul_eq_mul, ← hform_eq_toLinearMapₛₗ₂',
        ← hform_symm_of_involutive_of_hermitian σ hσ J hJ (v a) y0, hy0W a, map_zero, mul_zero]
    simp only [h0, Finset.sum_const_zero, sub_zero, ← hform_eq_toLinearMapₛₗ₂']
    rw [hform_symm_of_involutive_of_hermitian σ hσ J hJ]
    exact hz

private lemma Hf_e_e_eq_ite {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (hJd : J.det ≠ 0) :
    ∀ k, k ≤ n → ∃ v : Fin k → Fin n → E,
      (∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0) ∧
      ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hvo, hvd⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨y0, hy0W, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt
        (f := LinearMap.pi fun a => Matrix.toLinearMapₛₗ₂' E σ (RingHom.id E) J (v a))
        (by simpa only [Module.finrank_fin_fun] using Nat.lt_of_succ_le hk))
    have hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0 := fun a => by
      simpa only [hform_eq_toLinearMapₛₗ₂', LinearMap.pi_apply, Pi.zero_apply] using
        congrFun (LinearMap.mem_ker.mp hy0W) a
    obtain ⟨z, hz⟩ := exists_hform_ne_zero_of_det_ne_zero σ J hJd y0 hy0
    obtain ⟨p, hpW, hp⟩ := hermC_ppos_col_castLE σ hσ J hJ v hvo hvd z y0 hy0W hz
    have key : ∃ y, (∀ a, PI.NormGramAtOrigin.hform σ J (v a) y = 0) ∧
        PI.NormGramAtOrigin.hform σ J y y ≠ 0 := by
      by_contra! hcon
      refine hform_add_smul_self_ne_zero_of_isotropic_pair σ hσ J hJ p y0 (hcon p hpW)
        (hcon y0 hy0W) _ rfl hp (hcon _ fun a => ?_)
      rw [hform_eq_toLinearMapₛₗ₂', map_add, LinearMap.map_smulₛₗ, RingHom.id_apply, smul_eq_mul,
        ← hform_eq_toLinearMapₛₗ₂', ← hform_eq_toLinearMapₛₗ₂', hpW a, hy0W a, mul_zero, add_zero]
    obtain ⟨y, hyW, hyy⟩ := key
    refine ⟨Fin.snoc (α := fun _ => Fin n → E) v y, fun a b hab => ?_, fun a => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvo a b fun h => hab (congrArg Fin.castSucc h)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hyW a
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ, hyW b, map_zero]
      · exact absurd rfl hab
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvd a
      · simp only [Fin.snoc_last]
        exact hyy

theorem exists_nondegenerate : PI.NormGramAtOrigin.Statement := by
  unfold PI.NormGramAtOrigin.Statement
  intro E _ _ _ n r hr J hJ hJd
  have hσ : ∀ a : E, starRingEnd E (starRingEnd E a) = a := fun a => by simp
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    rw [starRingEnd_apply]
    exact hJ i j
  obtain ⟨v, hvo, hvd⟩ := Hf_e_e_eq_ite (starRingEnd E) hσ J hJ' hJd r hr
  refine ⟨v, ?_⟩
  have hg : PI.NormGramAtOrigin.gram (starRingEnd E) J v =
      Matrix.diagonal (fun a => PI.NormGramAtOrigin.hform (starRingEnd E) J (v a) (v a)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [PI.NormGramAtOrigin.gram]
    · simp [PI.NormGramAtOrigin.gram, Matrix.diagonal_apply_ne _ h, hvo a b h]
  rw [hg, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => hvd a
