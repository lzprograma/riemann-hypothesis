module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

open ArithmeticFunction Finset

noncomputable section

namespace Formalism.HC.Der.Rd

theorem sum_totient_pow {l : ℕ} (hl : l.Prime) (s : ℕ) : ∑ k ∈ range (s + 1), (l ^ k).totient = l ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow_succ hl, pow_succ]
    have h1 : 1 ≤ l := hl.one_lt.le
    calc l ^ s + l ^ s * (l - 1) = l ^ s * (1 + (l - 1)) := by ring
      _ = l ^ s * l := by congr 1; omega

theorem weight_sum {N m : ℕ} (hN : N ≠ 0) (hm : m ∣ N) (hm1 : m ≠ 1) :
    ∑ m' ∈ N.divisors.filter (fun m' => m ∣ m'), vonMangoldt m' * ((N / m').totient : ℝ) =
      (N.totient : ℝ) * (vonMangoldt m / (m.totient : ℝ)) := by
  by_cases hpp : IsPrimePow m
  swap
  · rw [vonMangoldt_eq_zero_iff.mpr hpp, zero_div, mul_zero]
    refine Finset.sum_eq_zero fun m' hm' => ?_
    rw [Finset.mem_filter] at hm'
    have h0 : vonMangoldt m' = 0 :=
      vonMangoldt_eq_zero_iff.mpr fun h => hpp (IsPrimePow.dvd h hm'.2 hm1)
    rw [h0, zero_mul]
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  obtain ⟨v, M, hpM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.one_lt.ne'
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have hdvd : ∀ k, p ^ k ∣ p ^ v * M ↔ k ≤ v := fun k =>
    ⟨fun h => (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
        ((Nat.Coprime.pow_left k hcop).dvd_of_dvd_mul_right h),
      fun h => (pow_dvd_pow p h).mul_right M⟩
  have hjv : j ≤ v := (hdvd j).mp hm
  have hsub : (range (v - j + 1)).image (fun i => p ^ (j + i)) ⊆
      (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m') := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨(hdvd _).mpr (by omega), hN⟩, pow_dvd_pow p (by omega)⟩
  have hzero : ∀ x ∈ (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m'),
      x ∉ (range (v - j + 1)).image (fun i => p ^ (j + i)) →
        vonMangoldt x * (((p ^ v * M) / x).totient : ℝ) = 0 := by
    intro x hx hxT
    rw [Finset.mem_filter, Nat.mem_divisors] at hx
    by_contra hne
    have hx' : vonMangoldt x ≠ 0 := fun h => hne (by rw [h, zero_mul])
    rw [Ne, vonMangoldt_eq_zero_iff, not_not, isPrimePow_nat_iff] at hx'
    obtain ⟨q, k, hq, hk, rfl⟩ := hx'
    have hpq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow ((dvd_pow_self p hj.ne').trans hx.2))
    subst hpq
    have hjk : j ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hx.2
    have hkv : k ≤ v := (hdvd k).mp hx.1.1
    apply hxT
    rw [Finset.mem_image]
    exact ⟨k - j, Finset.mem_range.mpr (by omega), by congr 1; omega⟩
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_image (by
    intro a _ b _ h
    have h2 : j + a = j + b := Nat.pow_right_injective hp.two_le h
    omega)]
  have hterm : ∀ i ∈ range (v - j + 1), vonMangoldt (p ^ (j + i)) * (((p ^ v * M) / p ^ (j + i)).totient : ℝ) =
      Real.log p * (((p ^ (v - j - i)).totient * M.totient : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    have h1 : p ^ v * M = p ^ (j + i) * (p ^ (v - j - i) * M) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [h1, Nat.mul_div_cancel_left _ (pow_pos hp.pos _), Nat.totient_mul (Nat.Coprime.pow_left _ hcop)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : ∑ i ∈ range (v - j + 1), (p ^ (v - j - i)).totient * M.totient = p ^ (v - j) * M.totient := by
    rw [← Finset.sum_mul, ← sum_totient_pow hp (v - j)]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 2
    omega
  rw [← Nat.cast_sum, hsum]
  have hphi : (p ^ v).totient = p ^ (v - j) * (p ^ j).totient := by
    rw [Nat.totient_prime_pow hp (by omega), Nat.totient_prime_pow hp hj, ← mul_assoc, ← pow_add]
    congr 2
    omega
  have hpj : ((p ^ j).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos hp.pos j)).ne'
  rw [vonMangoldt_apply_pow hj.ne', vonMangoldt_apply_prime hp,
    Nat.totient_mul (Nat.Coprime.pow_left v hcop), hphi]
  have e : ((p ^ j).totient : ℝ) * (Real.log p / ((p ^ j).totient : ℝ)) = Real.log p :=
    mul_div_cancel₀ _ hpj
  push_cast
  linear_combination (-((p : ℝ) ^ (v - j) * (M.totient : ℝ))) * e

variable {N : ℕ} [NeZero N]

theorem order_dvd_iff {m : ℕ} (hm : m ∣ N) (u : ZMod N) : addOrderOf (u - 1) ∣ m ↔ u.val ≡ 1 [MOD N / m] := by
  obtain ⟨d, hd⟩ := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (by rw [hd, zero_mul])
  have hdm : N / m = d := by
    rw [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)]
  have key : m • (u - 1) = (((m : ℤ) * ((u.val : ℤ) - 1) : ℤ) : ZMod N) := by
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_zmod_val]
  have hN : (N : ℤ) = (m : ℤ) * d := by exact_mod_cast hd
  rw [hdm, addOrderOf_dvd_iff_nsmul_eq_zero, key, CharP.intCast_eq_zero_iff (ZMod N) N, hN,
    mul_dvd_mul_iff_left (by exact_mod_cast hm0), Nat.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm]

theorem mem_ker_iff {f : ℕ} (hf : f ∣ N) (u : (ZMod N)ˣ) :
    u ∈ (ZMod.unitsMap hf).ker ↔ (u : ZMod N).val ≡ 1 [MOD f] := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, ← Nat.cast_one (R := ZMod f)]
  change ZMod.cast (u : ZMod N) = _ ↔ _
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]

def KK (N : ℕ) [NeZero N] (f : ℕ) : Finset (ZMod N)ˣ := univ.filter fun u => (u : ZMod N).val ≡ 1 [MOD f]

theorem mem_KK {f : ℕ} {u : (ZMod N)ˣ} : u ∈ KK N f ↔ (u : ZMod N).val ≡ 1 [MOD f] := by
  simp [KK]

theorem card_KK {f : ℕ} (hf : f ∣ N) : (KK N f).card * f.totient = N.totient := by
  classical
  have : NeZero f := ⟨(Nat.pos_of_dvd_of_pos hf (NeZero.pos N)).ne'⟩
  have h1 : (KK N f).card = Nat.card (ZMod.unitsMap hf).ker := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_of_subtype (p := fun u => u ∈ (ZMod.unitsMap hf).ker) _
      fun u => by rw [mem_KK, mem_ker_iff hf]).symm
  have h2 : (ZMod.unitsMap hf).ker.index = Nat.card (ZMod f)ˣ :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective hf)).toEquiv
  rw [h1, ← ZMod.card_units_eq_totient f, ← Nat.card_eq_fintype_card, ← h2, Subgroup.card_mul_index,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]


open Classical in
def rho (U : Subgroup (ZMod N)ˣ) (f : ℕ) : ℝ := by
  classical
  exact (((KK N f).filter fun u => u ∉ U).card : ℝ) * f.totient / N.totient

open Classical in
theorem abel (U : Subgroup (ZMod N)ˣ) :
    ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) =
      ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hT : (N.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'
  calc _ = ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        ∑ m ∈ N.divisors, (if addOrderOf ((u : ZMod N) - 1) ∣ m then
          vonMangoldt m * ((N / m).totient : ℝ) / N.totient else 0) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.mem_filter] at hu
        have hd : addOrderOf ((u : ZMod N) - 1) ∣ N :=
          addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
        have h1 : addOrderOf ((u : ZMod N) - 1) ≠ 1 := by
          intro h
          have h' := addOrderOf_nsmul_eq_zero ((u : ZMod N) - 1)
          rw [h, one_nsmul, sub_eq_zero] at h'
          exact hu.2 (by rw [show u = 1 from Units.ext (by rw [h', Units.val_one])]; exact one_mem U)
        rw [← Finset.sum_filter, ← Finset.sum_div, weight_sum hN hd h1, eq_div_iff hT]
        ring
    _ = ∑ m ∈ N.divisors, ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        (if addOrderOf ((u : ZMod N) - 1) ∣ m then
          vonMangoldt m * ((N / m).totient : ℝ) / N.totient else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmN : m ∣ N := Nat.dvd_of_mem_divisors hm
        have hcard : (((univ : Finset (ZMod N)ˣ).filter (fun u : (ZMod N)ˣ => u ∉ U)).filter
            (fun u : (ZMod N)ˣ => addOrderOf ((u : ZMod N) - 1) ∣ m)).card =
            ((KK N (N / m)).filter fun u => u ∉ U).card := by
          apply congrArg Finset.card
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_KK,
            order_dvd_iff hmN]
          tauto
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
        unfold rho
        ring

private theorem card_KK_ne_zero_of_dvd {f : ℕ} (hf : f ∣ N) : (KK N f).card ≠ 0 := by
  intro h
  have h' := card_KK hf
  rw [h, zero_mul] at h'
  exact (Nat.totient_pos.mpr (NeZero.pos N)).ne' h'.symm

theorem rho_nonneg (U : Subgroup (ZMod N)ˣ) (f : ℕ) : 0 ≤ rho U f := by
  unfold rho
  apply div_nonneg
  · positivity
  · exact le_of_lt (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N))

open Classical in
private theorem card_outside_add_card_inside (U : Subgroup (ZMod N)ˣ) (f : ℕ) :
    ((KK N f).filter fun u => u ∉ U).card +
      ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
  rw [add_comm]
  exact Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)

open Classical in
private theorem rho_eq_card_div (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
    rho U f = (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card := by
  have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
    exact_mod_cast card_KK hf
  have ht : (f.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hf (NeZero.pos N))).ne'
  have hK : ((KK N f).card : ℝ) ≠ 0 := by
    exact_mod_cast card_KK_ne_zero_of_dvd hf
  unfold rho
  rw [← hc]
  field_simp [ht, hK]

open Classical in
theorem rho_eq (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
    rho U f = 1 - (((KK N f).filter fun u => u ∈ U).card : ℝ) * f.totient / N.totient := by
  have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
    exact_mod_cast card_KK hf
  have ht : (f.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hf (NeZero.pos N))).ne'
  have hK : ((KK N f).card : ℝ) ≠ 0 := by exact_mod_cast card_KK_ne_zero_of_dvd hf
  have hs : (((KK N f).filter fun u => u ∉ U).card : ℝ) +
      (((KK N f).filter fun u => u ∈ U).card : ℝ) = (KK N f).card := by
    exact_mod_cast card_outside_add_card_inside U f
  rw [rho_eq_card_div U hf, ← hc, mul_div_mul_right _ _ ht, eq_sub_iff_add_eq, ← add_div, hs,
    div_self hK]

theorem one_mem_KK {f : ℕ} (hf : f ∣ N) : (1 : (ZMod N)ˣ) ∈ KK N f := by
  rw [mem_KK, ← mem_ker_iff hf]
  exact one_mem _

theorem mul_mem_KK {f : ℕ} (hf : f ∣ N) {u v : (ZMod N)ˣ} (hu : u ∈ KK N f) (hv : v ∈ KK N f) : u * v ∈ KK N f := by
  rw [mem_KK, ← mem_ker_iff hf] at hu hv ⊢
  exact mul_mem hu hv

theorem rho_le (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) : rho U f ≤ 1 - (f.totient : ℝ) / N.totient := by
  open Classical in
  have hB : (1 : ℝ) ≤ (((KK N f).filter fun u => u ∈ U).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨one_mem_KK hf, one_mem U⟩⟩
  rw [rho_eq U hf, mul_div_assoc]
  have h0 : (0 : ℝ) ≤ (f.totient : ℝ) / N.totient := by positivity
  nlinarith

private theorem card_filter_le_of_mul_maps {f : ℕ} (hf : f ∣ N)
    {p q : (ZMod N)ˣ → Prop} [DecidablePred p] [DecidablePred q]
    {u0 : (ZMod N)ˣ} (hu0 : u0 ∈ KK N f)
    (hmul : ∀ v ∈ KK N f, p v → q (u0 * v)) :
    ((KK N f).filter p).card ≤ ((KK N f).filter q).card := by
  refine Finset.card_le_card_of_injOn (fun v => u0 * v) ?_ (fun a _ b _ => mul_left_cancel)
  intro v hv
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv ⊢
  exact ⟨mul_mem_KK hf hu0 hv.1, hmul v hv.1 hv.2⟩

theorem half_le_rho (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) (h : ∃ u ∈ KK N f, u ∉ U) : 1 / 2 ≤ rho U f := by
  open Classical in
  obtain ⟨u0, hu0, hu0'⟩ := h
  have h1 : (((KK N f).filter fun u => u ∈ U).card : ℝ) ≤
      ((KK N f).filter fun u => u ∉ U).card :=
    Nat.cast_le.mpr <| card_filter_le_of_mul_maps hf (p := fun u => u ∈ U) (q := fun u => u ∉ U) hu0
      fun v _ hv hmem => hu0' <| by
        have h' := mul_mem hmem (inv_mem hv)
        rwa [mul_inv_cancel_right] at h'
  have h2 : (((KK N f).filter fun u => u ∉ U).card : ℝ) +
      ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
    exact_mod_cast card_outside_add_card_inside U f
  have hK : (0 : ℝ) < (KK N f).card :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))
  rw [rho_eq_card_div U hf, le_div_iff₀ hK]
  linarith

theorem rho_le_half (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N)
    (h : ∀ u ∈ KK N f, ∀ v ∈ KK N f, u ∉ U → v ∉ U → u * v ∈ U) : rho U f ≤ 1 / 2 := by
  open Classical in
  have h1 : (((KK N f).filter fun u => u ∉ U).card : ℝ) ≤
      ((KK N f).filter fun u => u ∈ U).card := by
    refine Nat.cast_le.mpr ?_
    rcases Finset.eq_empty_or_nonempty ((KK N f).filter fun u => u ∉ U) with he | ⟨u0, hu0⟩
    · rw [he, Finset.card_empty]
      exact Nat.zero_le _
    · rw [Finset.mem_filter] at hu0
      exact card_filter_le_of_mul_maps hf (p := fun u => u ∉ U) (q := fun u => u ∈ U) hu0.1
        fun v hv1 hv2 => h u0 hu0.1 v hv1 hu0.2 hv2
  have h2 : (((KK N f).filter fun u => u ∉ U).card : ℝ) +
      ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
    exact_mod_cast card_outside_add_card_inside U f
  have hK : (0 : ℝ) < (KK N f).card :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))
  rw [rho_eq_card_div U hf, div_le_iff₀ hK]
  linarith

theorem KK_gcd (U : Subgroup (ZMod N)ˣ) {a b : ℕ} (ha : a ∣ N) (hb : b ∣ N) (h1 : ∀ u ∈ KK N a, u ∈ U)
    (h2 : ∀ u ∈ KK N b, u ∈ U) : ∀ u ∈ KK N (Nat.gcd a b), u ∈ U := by
  intro u hu
  rw [mem_KK] at hu
  have hL : Nat.lcm a b ∣ N := Nat.lcm_dvd ha hb
  obtain ⟨k, hka, hkb⟩ := Nat.chineseRemainder' (hu.symm : 1 ≡ (u : ZMod N).val [MOD Nat.gcd a b])
  have hca : Nat.Coprime k a := by
    unfold Nat.Coprime
    rw [hka.gcd_eq, Nat.gcd_one_left]
  have hub : Nat.Coprime (u : ZMod N).val b :=
    Nat.Coprime.coprime_dvd_right hb (ZMod.val_coe_unit_coprime u)
  have hcb : Nat.Coprime k b := by
    unfold Nat.Coprime
    rw [hkb.gcd_eq]
    exact hub
  have hcop : Nat.Coprime k (Nat.lcm a b) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul a b) (Nat.Coprime.mul_right hca hcb)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hL (ZMod.unitOfCoprime k hcop)
  have hvk : (v : ZMod N).val ≡ k [MOD Nat.lcm a b] := by
    have h3 := congrArg (fun w : (ZMod (Nat.lcm a b))ˣ => (w : ZMod (Nat.lcm a b))) hv
    simp only [ZMod.coe_unitOfCoprime] at h3
    change ZMod.cast (v : ZMod N) = _ at h3
    rw [ZMod.cast_eq_val] at h3
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h3
  have hva : v ∈ U := h1 v (by
    rw [mem_KK]
    exact (hvk.of_dvd (Nat.dvd_lcm_left a b)).trans hka)
  have hvb : v⁻¹ * u ∈ U := h2 _ (by
    rw [mem_KK, ← mem_ker_iff hb, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    change ZMod.cast (v : ZMod N) = ZMod.cast (u : ZMod N)
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]
    exact (hvk.of_dvd (Nat.dvd_lcm_right a b)).trans hkb)
  have h4 := mul_mem hva hvb
  rwa [mul_inv_cancel_left] at h4

end Formalism.HC.Der.Rd

end
