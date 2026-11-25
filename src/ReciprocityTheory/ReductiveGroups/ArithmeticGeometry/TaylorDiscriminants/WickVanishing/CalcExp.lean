module

public import Mathlib.RingTheory.PowerSeries.Log

@[expose] public section

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

section Two

variable (k : Type) [CommRing k] [Algebra ℚ k]

theorem fin_two_finsupp_eq_iff (e : Fin 2 →₀ ℕ) (m l : ℕ) :
    e = Finsupp.single 0 m + Finsupp.single 1 l ↔ e 0 = m ∧ e 1 = l := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

theorem coeff_X_add_X_pow (e : Fin 2 →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff e (((X 0 : MvPowerSeries (Fin 2) k) + X 1) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : k) else 0 := by

  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1),
      MvPowerSeries.coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (n - m) *
        (n.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = n - m then (n.choose m : k) else 0 := by
    intro m _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, one_mul, MvPowerSeries.coeff_monomial]
    by_cases h : e 0 = m ∧ e 1 = n - m
    · rw [ite_eq_left h, ite_eq_left ((fin_two_finsupp_eq_iff e m (n - m)).2 h)]; simp
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((fin_two_finsupp_eq_iff e m (n - m)).1 h'))]; simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hn
  · rw [Finset.sum_eq_single (e 0)]
    · rw [ite_eq_left ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [ite_eq_right (fun h => hm h.1.symm)]
    · intro h
      exfalso; exact h (Finset.mem_range.mpr (by omega))
  · apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [ite_eq_right (fun h => hn (by omega))]

theorem exp_two :
    PowerSeries.subst ((X 0 : MvPowerSeries (Fin 2) k) + X 1) (PowerSeries.exp k) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  have hX : ∀ i : Fin 2, ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
        if d = Finsupp.single i (d i) then algebraMap ℚ k (1 / (d i).factorial) else 0 := by
    intro i d
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X i), finsum_eq_single _ (d i)]
    · rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, PowerSeries.coeff_exp]
      split_ifs <;> simp
    · intro m hm
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, ite_eq_right, smul_zero]
      intro h; apply hm; rw [h]; simp
  ext e
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
  · rw [hX, hX, ite_eq_left (by simp), ite_eq_left (by simp)]
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
      finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_X_add_X_pow, ite_eq_left rfl, PowerSeries.coeff_exp]
      simp only [Finsupp.single_eq_same, smul_eq_mul]
      rw [← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
      congr 1
      have hf0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1))
      rw [Nat.add_sub_cancel_left] at hf0
      have hf : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * (e 0).factorial * (e 1).factorial =
          (e 0 + e 1).factorial := by exact_mod_cast hf0
      have ha : ((e 0).factorial : ℚ) ≠ 0 := by positivity
      have hb : ((e 1).factorial : ℚ) ≠ 0 := by positivity
      have hc : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      rw [← hf]
      field_simp
    · intro m hm
      rw [coeff_X_add_X_pow, ite_eq_right (Ne.symm hm), smul_zero]
  · rintro ⟨p, q⟩ hpq' hne
    have hpq : p + q = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq'
    dsimp only
    rw [hX, hX]
    by_cases hp : p = Finsupp.single 0 (p 0)
    · by_cases hq : q = Finsupp.single 1 (q 1)
      · exfalso; apply hne
        have h0 : p 0 = e 0 := by rw [← hpq, hp, hq]; simp
        have h1 : q 1 = e 1 := by rw [← hpq, hp, hq]; simp
        rw [hp, hq, h0, h1]
      · rw [ite_eq_right hq, mul_zero]
    · rw [ite_eq_right hp, zero_mul]
  · intro h; exfalso; apply h
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr ((fin_two_finsupp_eq_iff e (e 0) (e 1)).2 ⟨rfl, rfl⟩).symm

end Two

section General

variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}

theorem hasSubst_two {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ k) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [ha, hb])

theorem subst_two_psubst {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (Y : MvPowerSeries (Fin 2) k) (hY : constantCoeff Y = 0) (f : PowerSeries k) :
    MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ k) (PowerSeries.subst Y f) =
      PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ k) Y) f := by
  have hY' := (PowerSeries.HasSubst.of_constantCoeff_zero hY).const
  exact MvPowerSeries.subst_comp_subst_apply hY' (hasSubst_two ha hb) f

theorem exp_add {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.subst (a + b) (PowerSeries.exp k) =
      PowerSeries.subst a (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k) := by
  have hab := hasSubst_two ha hb
  have h0 : constantCoeff ((X 0 : MvPowerSeries (Fin 2) k) + X 1) = 0 := by simp
  have e1 := subst_two_psubst ha hb _ h0 (PowerSeries.exp k)
  rw [exp_two k, MvPowerSeries.subst_mul hab, subst_two_psubst ha hb _ (by simp),
    subst_two_psubst ha hb _ (by simp), MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab,
    MvPowerSeries.subst_X hab] at e1
  simpa using e1.symm

theorem constantCoeff_psubst {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) (f : PowerSeries k) :
    constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : f = PowerSeries.C (PowerSeries.constantCoeff f) +
      (f - PowerSeries.C (PowerSeries.constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add (f := _),
    PowerSeries.constantCoeff_subst_eq_zero ha _ (by simp), add_zero]
  simp

theorem constantCoeff_exp {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    constantCoeff (PowerSeries.subst a (PowerSeries.exp k)) = 1 := by
  rw [constantCoeff_psubst ha, PowerSeries.constantCoeff_exp]

theorem exp_zero : PowerSeries.subst (0 : MvPowerSeries σ k) (PowerSeries.exp k) = 1 := by
  rw [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one, map_one]

end General

section Inj

variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}

theorem natCast_mul_eq_zero {x : k} {n : ℕ} (hn : n ≠ 0) (h : (n : k) * x = 0) : x = 0 := by
  have hu : IsUnit (n : k) := by
    rw [← map_natCast (algebraMap ℚ k)]
    exact (IsUnit.mk0 _ (by exact_mod_cast hn)).map _
  exact hu.mul_right_eq_zero.mp h

private theorem subst_log_subst_exp_sub_one_eq_self {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a (PowerSeries.exp k) - 1) (PowerSeries.log k) = a := by
  have ha' : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.subst a (PowerSeries.exp k) - 1 =
      PowerSeries.subst a (PowerSeries.exp k - 1) := by
    rw [← PowerSeries.coe_substAlgHom ha', map_sub, map_one]
  have hs : PowerSeries.HasSubst (PowerSeries.exp k - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [h1, ← PowerSeries.subst_comp_subst_apply hs ha', PowerSeries.subst_log_exp_sub_one, PowerSeries.subst_X ha']

theorem eq_zero_of_exp_eq_one {c : MvPowerSeries σ k} (hc : constantCoeff c = 0)
    (h : PowerSeries.subst c (PowerSeries.exp k) = 1) : c = 0 := by
  have h1 := subst_log_subst_exp_sub_one_eq_self hc
  rw [h, sub_self, PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log] at h1
  exact h1.symm

theorem exp_inj {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (h : PowerSeries.subst a (PowerSeries.exp k) = PowerSeries.subst b (PowerSeries.exp k)) : a = b := by
  have hab : constantCoeff (a - b) = 0 := by simp [ha, hb]
  have h1 := exp_add hab hb
  rw [sub_add_cancel, h] at h1
  have hu : IsUnit (PowerSeries.subst b (PowerSeries.exp k)) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_exp hb]; exact isUnit_one)
  have h3 : 1 * PowerSeries.subst b (PowerSeries.exp k) =
      PowerSeries.subst (a - b) (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k) :=
    (one_mul _).trans h1
  exact sub_eq_zero.mp (eq_zero_of_exp_eq_one hab (hu.mul_right_cancel h3).symm)

end Inj

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}

theorem constantCoeff_logS {f : MvPowerSeries σ k} (hf : constantCoeff f = 1) :
    constantCoeff (PowerSeries.subst (f - 1) (PowerSeries.log k)) = 0 := PowerSeries.constantCoeff_subst_eq_zero (by simp [hf]) _ PowerSeries.constantCoeff_log

theorem exp_log {f : MvPowerSeries σ k} (hf : constantCoeff f = 1) :
    PowerSeries.subst (PowerSeries.subst (f - 1) (PowerSeries.log k)) (PowerSeries.exp k) = f := by
  have hb : PowerSeries.HasSubst (f - 1) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hf])
  have ha : PowerSeries.HasSubst (PowerSeries.log k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_log
  rw [← PowerSeries.subst_comp_subst_apply ha hb, PowerSeries.subst_exp_log,
    ← PowerSeries.coe_substAlgHom hb, map_add, PowerSeries.substAlgHom_X, map_one]
  ring

alias log_exp := _root_.ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_log_subst_exp_sub_one_eq_self

end Log

section Props

theorem subst_exp {k : Type} [CommRing k] [Algebra ℚ k] {σ τ : Type} [Finite σ] (φ : σ → MvPowerSeries τ k)
    (hφ : ∀ s, constantCoeff (φ s) = 0) {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    MvPowerSeries.subst φ (PowerSeries.subst a (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst φ a) (PowerSeries.exp k) := by
  have ha' := (PowerSeries.HasSubst.of_constantCoeff_zero ha).const
  exact MvPowerSeries.subst_comp_subst_apply ha' (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ) _

end Props

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
