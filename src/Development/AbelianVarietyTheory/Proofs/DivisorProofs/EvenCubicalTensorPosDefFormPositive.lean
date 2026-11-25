module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TPos

open Finset

theorem lagrange_decomp : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ), (∀ i j, A i j = A j i) →
    (∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (A i j : ℚ) * v j) →
    ∃ N : ℕ, 0 < N ∧ ∃ (k : ℕ) (n : Fin k → ℕ) (m : Fin k → Fin r → ℤ),
      ∀ i j, (N : ℤ) * A i j = ∑ l, (n l : ℤ) * m l i * m l j := by
  intro r
  induction r with
  | zero => intro A _ _; exact ⟨1, one_pos, 0, Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro A hs hp
    have ha : 0 < A 0 0 := by
      simpa [Fin.sum_univ_succ, Fin.succ_ne_zero] using
        hp (fun i => if i = 0 then 1 else 0) fun h => by simpa using congrFun h 0
    set a := A 0 0
    set c : Fin r → ℤ := fun j => A 0 j.succ
    set S : Matrix (Fin r) (Fin r) ℤ := fun i j => a * A i.succ j.succ - c i * c j
    have hSs : ∀ i j, S i j = S j i := fun i j => by simp only [S, hs i.succ j.succ]; ring
    have hSp : ∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (S i j : ℚ) * v j := fun v hv => by
      set s : ℚ := ∑ j, (c j : ℚ) * v j
      set Q : ℚ := ∑ i, ∑ j, v i * (A i.succ j.succ : ℚ) * v j
      have haq : (0:ℚ) < a := by exact_mod_cast ha
      have h1 : ∑ i, ∑ j, v i * (S i j : ℚ) * v j = a * Q - s * s := by
        have e : ∀ i j, v i * (S i j : ℚ) * v j =
            a * (v i * (A i.succ j.succ : ℚ) * v j) - ((c i : ℚ) * v i) * ((c j : ℚ) * v j) := fun i j => by
          rw [show S i j = a * A i.succ j.succ - c i * c j from rfl]; push_cast; ring
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j,
          Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      set u : Fin (r+1) → ℚ := Fin.cons (-s / a) v
      have hu0 : u ≠ 0 := fun h => hv (funext fun j => by simpa [u] using congrFun h j.succ)
      have h2 : ∑ i, ∑ j, u i * (A i j : ℚ) * u j = Q - s * s / a := by
        simp only [Fin.sum_univ_succ, u, Fin.cons_zero, Fin.cons_succ]
        have e1 : ∑ j : Fin r, -s / a * (A 0 j.succ : ℚ) * v j = -s / a * s := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by simp only [c]; ring
        have e2 : ∑ i : Fin r, (v i * (A i.succ 0 : ℚ) * (-s / a) +
            ∑ j : Fin r, v i * (A i.succ j.succ : ℚ) * v j) = -s / a * s + Q := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [hs i.succ 0]; simp only [c]; ring
        rw [e1, e2]; field_simp; ring
      rw [h1, show a * Q - s * s = a * (Q - s * s / a) by field_simp, ← h2]
      exact mul_pos haq (hp u hu0)
    obtain ⟨N', hN', k, n, m, hm⟩ := ih S hSs hSp
    refine ⟨N' * a.toNat, Nat.mul_pos hN' (by lia), k + 1, Fin.cons N' n,
      Fin.cons (fun j => A 0 j) (fun l => Fin.cons 0 (m l)), fun i j => ?_⟩
    have haN : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_mul, haN]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [a]
    · simp [a]
    · simp; rw [hs i.succ 0]; ring
    · simp only [Fin.cons_succ]; rw [← hm i j]; simp only [S, c]; ring

theorem tensor_pos : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ z : Fin r → X, z ≠ 0 → ∃ s ∈ maximalIdeal R, ((∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s := by
  intro R _ _ _ _ _ X _ _ κ hneg hcub hmax r W hW z hz
  classical
  let B : X → X → (FractionRing R)ˣ := fun a b => κ (a + b) * (κ a)⁻¹ * (κ b)⁻¹
  have h0 : κ 0 = 1 := mul_left_cancel (a := κ 0 * κ 0 * κ 0) (by simpa [add_zero] using hcub 0 0 0)
  have hB1 : ∀ a a' b, B (a + a') b = B a b * B a' b := fun a a' b => by
    have e : κ (a + a' + b) = κ (a + a') * κ (a + b) * κ (a' + b) * (κ a * κ a' * κ b)⁻¹ := by
      rw [← hcub a a' b]; group
    simp only [B]; rw [e]; ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := (κ a).ne_zero; have := (κ a').ne_zero; have := (κ b).ne_zero
    have := (κ (a + a')).ne_zero; have := (κ (a + b)).ne_zero; have := (κ (a' + b)).ne_zero
    field_simp
  have hBs : ∀ a b, B a b = B b a := fun a b => by simp only [B, add_comm]; exact mul_right_comm _ _ _
  have hB0 : ∀ b, B 0 b = 1 := fun b => by simp [B, h0]
  have hBd : ∀ a, B a a = κ a ^ 2 := fun a => by
    have h := hB1 a (-a) a
    rw [add_neg_cancel, hB0, show B (-a) a = (κ a)⁻¹ * (κ a)⁻¹ by simp [B, h0, hneg]] at h
    rw [eq_inv_of_mul_eq_one_left h.symm]; group
  let f : X → Multiplicative X →* (FractionRing R)ˣ := fun w =>
    { toFun := fun a => B (Multiplicative.toAdd a) w, map_one' := hB0 w, map_mul' := fun a b => hB1 _ _ _ }
  have hBsum : ∀ (c : Fin r → ℤ) (w : X), B (∑ i, c i • z i) w = ∏ i, B (z i) w ^ c i := fun c w => by
    have e : Multiplicative.ofAdd (∑ i, c i • z i) = ∏ i, (Multiplicative.ofAdd (z i)) ^ c i := by
      simp [ofAdd_sum, ofAdd_zsmul]
    have := congrArg (f w) e
    rw [map_prod] at this
    simp only [map_zpow] at this
    exact this
  have hBn : ∀ (M : ℕ) a w, B (M • a) w = B a w ^ M := fun M a w =>
    Nat.rec (by simp [hB0]) (fun _ ih => by rw [succ_nsmul, hB1, ih, pow_succ]) M
  have hQ : ∀ c : Fin r → ℤ, ∏ i, ∏ j, B (z i) (z j) ^ (c i * c j) = κ (∑ i, c i • z i) ^ 2 := fun c => by
    rw [← hBd, hBsum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hBs, hBsum, ← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun j _ => by rw [hBs, ← zpow_mul, mul_comm]
  set A : Matrix (Fin r) (Fin r) ℤ := W + W.transpose
  have hApos : ∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (A i j : ℚ) * v j := fun v hv => by
    have hv' : (fun i => (v i : ℝ)) ≠ 0 := fun h => hv (funext fun i => by have := congrFun h i; simpa using this)
    have h := hW.dotProduct_mulVec_pos hv'
    have e : dotProduct (star (fun i => (v i : ℝ))) ((A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (v i : ℝ))) =
        ((∑ i, ∑ j, v i * (A i j : ℚ) * v j : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Rat.cast_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    exact_mod_cast e ▸ h
  obtain ⟨N, hN, k, n, m, hm⟩ := lagrange_decomp r A (fun i j => add_comm (W i j) (W j i)) hApos
  set x : (FractionRing R)ˣ := ∏ i, ∏ j, B (z i) (z j) ^ W i j
  have hx2 : x ^ 2 = ∏ i, ∏ j, B (z i) (z j) ^ A i j := by
    have e1 : ∏ i, ∏ j, B (z i) (z j) ^ A i j =
        (∏ i, ∏ j, B (z i) (z j) ^ W i j) * ∏ i, ∏ j, B (z i) (z j) ^ W j i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun j _ => by rw [show A i j = W i j + W j i from rfl, zpow_add]
    have e2 : ∏ i, ∏ j, B (z i) (z j) ^ W j i = ∏ i, ∏ j, B (z i) (z j) ^ W i j := by
      rw [Finset.prod_comm]; exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [hBs]
    rw [e1, e2, pow_two]
  let y : Fin k → X := fun l => ∑ i, m l i • z i
  have hxN : x ^ (2 * N) = ∏ l, κ (y l) ^ (2 * n l) := calc
    x ^ (2 * N) = (x ^ 2) ^ N := pow_mul x 2 N
    _ = ∏ i, ∏ j, B (z i) (z j) ^ ((N : ℤ) * A i j) := by
      rw [hx2, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm]
    _ = ∏ i, ∏ j, ∏ l, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) :=
      Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by
        rw [hm, _root_.GlobalTheory.SharpFamRel.zpow_finsetSum]
        exact Finset.prod_congr rfl fun l _ => by rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
    _ = ∏ i, ∏ l, ∏ j, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) := Finset.prod_congr rfl fun _ _ => Finset.prod_comm
    _ = ∏ l, ∏ i, ∏ j, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) := Finset.prod_comm
    _ = ∏ l, κ (y l) ^ (2 * n l) := Finset.prod_congr rfl fun l _ => by
      rw [pow_mul, show y l = ∑ i, m l i • z i from rfl, ← hQ (m l)]; simp only [Finset.prod_pow]
  have hs : ∀ l, ∃ t : R, ((κ (y l) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ t ∧
      (y l ≠ 0 → t ∈ maximalIdeal R) := fun l =>
    if h : y l = 0 then ⟨1, by rw [h, h0]; simp, fun h' => absurd h h'⟩
    else let ⟨t, ht, e⟩ := hmax _ h; ⟨t, e, fun _ => ht⟩
  choose s hs1 hs2 using hs
  have hxK : ((x : (FractionRing R)ˣ) : FractionRing R) ^ (2 * N) = algebraMap R _ (∏ l, s l ^ (2 * n l)) := by
    rw [← Units.val_pow_eq_pow_val, hxN, Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun l _ => by rw [Units.val_pow_eq_pow_val, hs1, map_pow]
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (IsIntegral.of_pow (by lia : 0 < 2 * N) (hxK ▸ isIntegral_algebraMap))
  have htN : t ^ (2 * N) = ∏ l, s l ^ (2 * n l) :=
    IsFractionRing.injective R (FractionRing R) (by rw [map_pow, ht, hxK])
  have hdet : A.det ≠ 0 := by
    have h := hW.det_pos
    have e : (A.map (Int.cast : ℤ → ℝ)).det = ((A.det : ℤ) : ℝ) := ((Int.castRingHom ℝ).map_det A).symm
    rw [e] at h; exact_mod_cast h.ne'
  have hex : ∃ l, n l ≠ 0 ∧ y l ≠ 0 := by
    by_contra! hcon
    have hrow : ∀ i, ∑ j, ((N : ℤ) * A i j) • z j = 0 := fun i => by
      simp_rw [hm i, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [show ∑ j, ((n l : ℤ) * m l i * m l j) • z j = ((n l : ℤ) * m l i) • y l by
        simp only [y, Finset.smul_sum, mul_smul]]
      by_cases hn : n l = 0
      · simp [hn]
      · rw [hcon l hn, smul_zero]
    have hcol : ∀ q, ((N : ℤ) * A.det) • z q = 0 := fun q => by
      have h1 : ∑ i, A.adjugate q i • ∑ j, ((N : ℤ) * A i j) • z j = 0 := by simp [hrow]
      rw [← h1]
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, show ∀ j, ∑ i, A.adjugate q i * ((N : ℤ) * A i j) = (N : ℤ) * (A.adjugate * A) q j from
        fun j => by rw [Matrix.mul_apply, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      simp [Finset.sum_ite_eq, mul_comm]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hz
    have hD : (N : ℤ) * A.det ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') hdet
    have hM : ((N : ℤ) * A.det).natAbs • z q = 0 := by
      rcases Int.natAbs_eq ((N : ℤ) * A.det) with h | h
      · rw [← natCast_zsmul, ← h]; exact hcol q
      · have := hcol q; rw [h, neg_smul, neg_eq_zero, natCast_zsmul] at this; exact this
    have hk1 : κ (z q) ^ (2 * ((N : ℤ) * A.det).natAbs) = 1 := by rw [pow_mul, ← hBd, ← hBn, hM, hB0]
    obtain ⟨s', hs', e'⟩ := hmax _ hq
    have h1 : s' ^ (2 * ((N : ℤ) * A.det).natAbs) = 1 := IsFractionRing.injective R (FractionRing R)
      (by rw [map_pow, ← e', map_one, ← Units.val_pow_eq_pow_val, hk1, Units.val_one])
    exact (IsLocalRing.mem_maximalIdeal _).mp hs' (IsUnit.of_pow_eq_one h1 (by have := Int.natAbs_pos.mpr hD; lia))
  obtain ⟨l0, hn0, hy0⟩ := hex
  have hprod : ∏ l, s l ^ (2 * n l) ∈ maximalIdeal R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l0)]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (hs2 l0 hy0) _ (by lia))
  exact ⟨t, (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem (2 * N) (htN ▸ hprod), ht.symm⟩

end GlobalTheory.Mum.TPos
