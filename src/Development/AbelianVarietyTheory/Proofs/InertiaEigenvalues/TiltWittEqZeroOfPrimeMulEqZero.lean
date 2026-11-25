module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl

namespace GlobalTheory.HWL.TensorWitt

section Coord

variable {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
  (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W]

theorem mem_pow_iff (w : W) (n : ℕ) (x : O ⊗[Z] W) :
    x ∈ Ideal.span {((1 : O) ⊗ₜ[Z] w) ^ n} ↔ ∀ i, crd b i x ∈ Ideal.span {w ^ n} := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Ideal.mem_span_singleton]
  simp_rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨crd b i y, crd_mul b _ i y⟩
  · intro h
    choose c hc using h
    refine ⟨∑ i, b i ⊗ₜ[Z] c i, ?_⟩
    conv_lhs => rw [← _root_.GlobalTheory.Decompl.sum_crd b x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, Algebra.TensorProduct.tmul_mul_tmul, one_mul]


include b in
theorem complete_tensor (w : W) [h : IsAdicComplete (Ideal.span {w}) W] :
    IsAdicComplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
  have key : ∀ (n : ℕ) (x : O ⊗[Z] W),
      x ∈ (Ideal.span {(1 : O) ⊗ₜ[Z] w} ^ n • ⊤ : Submodule (O ⊗[Z] W) (O ⊗[Z] W)) ↔
        ∀ i, crd b i x ∈ (Ideal.span {w} ^ n • ⊤ : Submodule W W) := by
    intro n x
    simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact mem_pow_iff b w n x
  have H1 : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun x hx => ?_⟩
    have hi : ∀ i, crd b i x = 0 := fun i =>
      IsHausdorff.haus h.toIsHausdorff _ fun n => by
        rw [SModEq.sub_mem, sub_zero]
        exact (key n x).1 (by simpa [SModEq.sub_mem] using hx n) i
    rw [← _root_.GlobalTheory.Decompl.sum_crd b x]
    simp [hi]
  have H2 : IsPrecomplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun f hf => ?_⟩
    have hfi : ∀ i, ∃ L : W, ∀ n,
        crd b i (f n) ≡ L [SMOD (Ideal.span {w} ^ n • ⊤ : Submodule W W)] := fun i =>
      IsPrecomplete.prec h.toIsPrecomplete fun {m n} hmn => by
        rw [SModEq.sub_mem, ← map_sub]
        exact (key m _).1 (SModEq.sub_mem.1 (hf hmn)) i
    choose L hL using hfi
    refine ⟨∑ i, b i ⊗ₜ[Z] L i, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    rw [map_sub, crd_sum]
    exact SModEq.sub_mem.1 (hL i n)
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

end Coord

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) := by
  unfold inclW
  exact WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem tiltWitt_eq_zero_of_prime_mul_eq_zero (x : WCb l) (h : ((l : ℕ) : WCb l) * x = 0) : x = 0 := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  ext n
  have h1 := WittVector.mul_charP_coeff_succ (p := l) x n
  rw [mul_comm, h, WittVector.zero_coeff] at h1
  rw [WittVector.zero_coeff]
  exact (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero).1 h1.symm

theorem ainf_saturated_in_tiltWitt_prime (a : Loc.Ainf l) (w : WCb l) (h : inclW l a = ((l : ℕ) : WCb l) * w) :
    ∃ a', inclW l a' = w := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  refine ⟨WittVector.mk l fun n => (frobeniusEquiv (OCb l) l).symm (a.coeff (n + 1)), ?_⟩
  ext n
  have h1 := congrArg (fun z : WCb l => z.coeff (n + 1)) h
  simp only [inclW, WittVector.map_coeff] at h1
  rw [mul_comm, WittVector.mul_charP_coeff_succ] at h1
  apply frobenius_inj (Cb l) l
  simp only [inclW, WittVector.map_coeff]
  rw [← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, h1, frobenius_def]

theorem not_isUnit_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    ¬ IsUnit (WittVector.teichmuller l e - 1 : Loc.Ainf l) := by
  intro hu
  apply he
  have h1 := hu.map (WittVector.constantCoeff : WittVector l (OCb l) →+* OCb l)
  rwa [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h1

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (Ideal.span {((l : ℕ) : RW LL)}) (RW LL) ∧
    (∀ x : RW LL, ((l : ℕ) : RW LL) * x = 0 → x = 0) ∧ Function.Injective (inclR LL) ∧
    (∀ (y : RA LL) (x : RW LL), inclR LL y = ((l : ℕ) : RW LL) * x → ∃ y', inclR LL y' = x) ∧
    ∀ e : OCb l, ¬ IsUnit (e - 1) →
      IsAdicComplete (Ideal.span {(1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1)})
        (RA LL) := by
  intro l _ LL
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  have hl : ((l : ℕ) : RW LL) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) := by
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    haveI : IsAdicComplete (Ideal.span {((l : ℕ) : WCb l)}) (WCb l) :=
      (GlobalTheory.Per.AinfComplete.witt_complete (p := l) (R := Cb l) ((l : ℕ) : WCb l)
        (fun c => ⟨c, fun n => by simp⟩)
        (fun x hx => by simpa using hx 1)).2
    exact complete_tensor (basisO LL) _
  · intro x hx
    refine ext_crd (basisO LL) fun i => ?_
    rw [map_zero]
    exact tiltWitt_eq_zero_of_prime_mul_eq_zero _
      (by rw [← crd_natCast_mul (basisO LL) l i x, hx, map_zero])
  · intro y y' h
    exact ext_crd (basisO LL) fun i => inclW_injective (by rw [← crd_inclR, ← crd_inclR, h])
  · intro y x hyx
    have hi : ∀ i, ∃ a' : Loc.Ainf l, inclW l a' = crd (basisO LL) i x := fun i =>
      ainf_saturated_in_tiltWitt_prime (crd (basisO LL) i y) (crd (basisO LL) i x)
        ((crd_inclR LL i y).symm.trans
          ((congrArg (crd (basisO LL) i) hyx).trans (crd_natCast_mul (basisO LL) l i x)))
    choose a' ha' using hi
    refine ⟨∑ i, basisO LL i ⊗ₜ[ℤ_[l]] a' i, ext_crd (basisO LL) fun i => ?_⟩
    exact (crd_inclR LL i _).trans
      ((congrArg (inclW l) (crd_sum (basisO LL) a' i)).trans (ha' i))
  · intro e he
    haveI : IsAdicComplete (Ideal.span {(WittVector.teichmuller l e - 1 : Ainf l)}) (Ainf l) :=
      (GlobalTheory.Per.AinfComplete.main l _ (not_isUnit_teich e he)).2
    exact complete_tensor (basisO LL) _

end GlobalTheory.HWL.TensorWitt
