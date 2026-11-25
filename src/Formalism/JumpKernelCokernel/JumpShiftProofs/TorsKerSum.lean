module

public import Formalism.JumpKernelCokernel.Statement
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelSumLemmas

open PowerSeries

variable {O : Type} [CommRing O]

theorem len_pow [IsDomain O] (ℓ : O) (hℓ : ℓ ≠ 0) (k : ℕ) :
    Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  induction k with
  | zero =>
    have hs : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
    rw [Module.length_eq_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>

    have hle : Ideal.span {ℓ} ≤ Submodule.comap (LinearMap.mulLeft O (ℓ ^ k)) (Ideal.span {ℓ ^ (k + 1)}) := by
      intro x hx
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      exact Ideal.mem_span_singleton.mpr ⟨y, by ring⟩
    have hge : Ideal.span {ℓ ^ (k + 1)} ≤ Ideal.span {ℓ ^ k} :=
      Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ k.le_succ)
    have hk : ℓ ^ k ≠ 0 := pow_ne_zero k hℓ
    have hf : Function.Injective (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
        Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at hx
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, mul_left_cancel₀ hk ?_⟩
      rw [hc]
      ring
    have hg : Function.Surjective (Submodule.factor hge) := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk a, rfl⟩
    have hex : Function.Exact (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle) (Submodule.factor hge) := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      constructor
      · intro h
        have h' : a ∈ Ideal.span {ℓ ^ k} := by
          rw [← Submodule.Quotient.mk_eq_zero]
          exact h
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h'
        exact ⟨Submodule.Quotient.mk c, by rw [Submodule.mapQ_apply, LinearMap.mulLeft_apply, hc]⟩
      · rintro ⟨x, hx⟩
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [← hx, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
        show (Submodule.Quotient.mk (ℓ ^ k * c) : O ⧸ Ideal.span {ℓ ^ k}) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    rw [Module.length_eq_add_of_exact _ _ hf hg hex, ih]
    push_cast
    ring

abbrev J (ℓ : O) (n k : ℕ) : Ideal (PowerSeries O) :=
  Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

theorem coeff_dvd_of_mem (ℓ : O) (n k : ℕ) {r : PowerSeries O} (hr : r ∈ J ℓ n k) :
    ∀ i < n, ℓ ^ k ∣ coeff i r := by
  intro i hi
  obtain ⟨a, c, rfl⟩ := Ideal.mem_span_pair.mp hr
  rw [map_add (f := _), coeff_mul_X_pow', ite_eq_right (by omega), zero_add, coeff_mul_C]
  exact dvd_mul_left _ _

theorem mem_of_coeff_dvd (ℓ : O) (n k : ℕ) (p : PowerSeries O)
    (hp : ∀ i < n, ℓ ^ k ∣ coeff i p) : p ∈ J ℓ n k := by
  have hp' : ∀ i < n, ∃ c, coeff i p = ℓ ^ k * c := fun i hi => hp i hi
  choose! c hc using hp'
  refine Ideal.mem_span_pair.mpr
    ⟨PowerSeries.mk fun j => coeff (j + n) p, PowerSeries.mk fun i => if i < n then c i else 0, ?_⟩
  ext i
  rw [map_add (f := _), coeff_mul_X_pow', coeff_mul_C, coeff_mk, coeff_mk]
  split_ifs with h1 h2 h2
  · omega
  · rw [Nat.sub_add_cancel h1]
    ring
  · rw [hc i h2]
    ring
  · omega

theorem coeff_step (ℓ : O) (p : PowerSeries O) (i : ℕ) :
    coeff i p = coeff (i + 1) ((X - C ℓ) * p) + ℓ * coeff (i + 1) p := by
  rw [sub_mul, map_sub, coeff_succ_X_mul, coeff_C_mul]
  ring

theorem all_coeff_dvd (ℓ : O) (n k : ℕ) (p : PowerSeries O) (hp : (X - C ℓ) * p ∈ J ℓ n k)
    (htop : ℓ ^ k ∣ coeff (n - 1) p) : ∀ i < n, ℓ ^ k ∣ coeff i p := by

  have key : ∀ j i, i + j = n - 1 → i < n → ℓ ^ k ∣ coeff i p := by
    intro j
    induction j with
    | zero =>
      intro i hij _
      rw [show i = n - 1 by omega]
      exact htop
    | succ j ih =>
      intro i hij hi
      rw [Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_step ℓ p i]
      exact dvd_add (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k hp (i + 1) (by omega))
        (dvd_mul_of_dvd_right (ih (i + 1) (by omega) (by omega)) _)
  intro i hi
  exact key (n - 1 - i) i (by omega) hi

def lift (ℓ : O) (n k : ℕ) : (PowerSeries O ⧸ J ℓ n k) → PowerSeries O :=
  Function.surjInv Ideal.Quotient.mk_surjective

theorem mk_lift (ℓ : O) (n k : ℕ) (b : PowerSeries O ⧸ J ℓ n k) :
    Ideal.Quotient.mk (J ℓ n k) (lift ℓ n k b) = b := Function.surjInv_eq Ideal.Quotient.mk_surjective b

def topFun (ℓ : O) (n k : ℕ) (b : PowerSeries O ⧸ J ℓ n k) : O ⧸ Ideal.span {ℓ ^ k} :=
  Ideal.Quotient.mk _ (coeff (n - 1) (lift ℓ n k b))

theorem topFun_mk (ℓ : O) (n k : ℕ) (hn : 0 < n) (p : PowerSeries O) :
    topFun ℓ n k (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (coeff (n - 1) p) := by
  unfold Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have h := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mk_lift ℓ n k (Ideal.Quotient.mk _ p)
  rw [Ideal.Quotient.eq] at h
  have h2 := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k h (n - 1) (by omega)
  rwa [map_sub] at h2

def topMap (ℓ : O) (n k : ℕ) (hn : 0 < n) :
    (PowerSeries O ⧸ J ℓ n k) →ₗ[O] O ⧸ Ideal.span {ℓ ^ k} where
  toFun := topFun ℓ n k
  map_add' a b := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add (f := _), topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, map_add (f := _), map_add (f := _)]
  map_smul' c a := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
      topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, PowerSeries.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, coeff_C_mul]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]

theorem single (ℓ : O) (n k : ℕ) [IsDomain O] (hℓ : ℓ ≠ 0) :
    Module.length O (LinearMap.ker (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : (X : PowerSeries O) ^ 0 ∈ J ℓ 0 k := Ideal.subset_span (Set.mem_insert _ _)
    rw [pow_zero] at h1
    have hs : Subsingleton (PowerSeries O ⧸ J ℓ 0 k) :=
      Ideal.Quotient.subsingleton_iff.mpr ((Ideal.eq_top_iff_one _).mpr h1)
    rw [Module.length_eq_zero]
    exact zero_le
  ·
    have hinj : Function.Injective ((topMap ℓ n k hn).comp (LinearMap.ker (LinearMap.mulLeft O
        (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))).subtype) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨b, hb⟩ hT
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hb' := hb
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hb'
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply] at hT
      have hT' : topFun ℓ n k (Ideal.Quotient.mk _ p) = 0 := hT
      rw [Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun_mk ℓ n k hn, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton] at hT'
      have hpJ := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mem_of_coeff_dvd ℓ n k p
        (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.all_coeff_dvd ℓ n k p hb' hT')
      apply Subtype.ext
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpJ
    calc _ ≤ Module.length O (O ⧸ Ideal.span {ℓ ^ k}) := Module.length_le_of_injective _ hinj
      _ = _ := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow ℓ hℓ k

end Formalism.KernelCokernelLengths.TorsionKernelSumLemmas
