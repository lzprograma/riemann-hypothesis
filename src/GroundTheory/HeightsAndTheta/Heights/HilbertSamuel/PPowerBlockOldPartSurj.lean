module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockOldPartSurj
import Mathlib.Algebra.Order.Star.Int

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace PowerBlockOldPartSurj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def chartMon (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k

theorem homog_chartMon (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMon c d) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_one (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_mul (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_pow (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_X ⟨k, c k⟩) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rw [e] at this
  exact this

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod]

theorem eval_chartMon (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod]

theorem mem_of_homog {y : (Σ k, ι k) → Ω} {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [_root_.GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0]
  simp

theorem exists_chart_at {y : (Σ k, ι k) → Ω} {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hx.1
  refine ⟨c, hc, fun k h0 => hc k ?_⟩
  have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
    show X _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  simpa using hx.2 _ hX

theorem exists_common_forms (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ)
    (m N : ℕ) (v : Fin N → Ω) (hv : ∀ j, v j ∈ chartLat y a m) :
    ∃ (L E : K → ℕ) (G : Fin N → MRing ι), (∀ j, IsMultiHomog (G j) E) ∧ (∀ k, (E k : ℤ) = m * a k + L k) ∧
      ∀ j, aeval y (G j) = v j * ∏ k, y ⟨k, c k⟩ ^ L k := by
  choose Nj δ G hG hdeg hGv using fun j => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.exists_chartForm y c hc (fun k => (m : ℤ) * a k) (hv j c hc)
  have hN : ∀ j k, Nj j k ≤ ∑ i, Nj i k := fun j k =>
    Finset.single_le_sum (f := fun i => Nj i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set L : K → ℕ := fun k => ∑ i, Nj i k + ((m : ℤ) * a k).natAbs with hL
  refine ⟨L, fun k => ((L k : ℤ) + m * a k).toNat, fun j => G j * chartMon c (L - Nj j),
    fun j => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_congr (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_mul (hG j) (homog_chartMon c _)) fun k => ?_, fun k => ?_, fun j => ?_⟩
  · have h1 := hdeg j k
    have h2 := hN j k
    simp only [Pi.add_apply, Pi.sub_apply, hL]
    generalize (m : ℤ) * a k = q at *
    generalize ∑ i, Nj i k = S at *
    omega
  · simp only [hL]
    generalize (m : ℤ) * a k = q
    generalize ∑ i, Nj i k = S
    omega
  · rw [map_mul, hGv j, aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, Pi.sub_apply]
    congr 1
    have h2 := hN j k
    simp only [hL]
    omega

theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {m N : ℕ}
    {v : Fin N → Ω} (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * a k) v) {L E : K → ℕ} {G : Fin N → MRing ι}
    (hG : ∀ j, IsMultiHomog (G j) E) (hE : ∀ k, (E k : ℤ) = m * a k + L k)
    (hGy : ∀ j, aeval y (G j) = v j * ∏ k, y ⟨k, c k⟩ ^ L k)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) (hxc : ∀ k, x ⟨k, c k⟩ ≠ 0) :
    ∃ j, eval x (map (Int.castRingHom ℂ) (G j)) ≠ 0 := by
  obtain ⟨u, hu, hsum⟩ := hgen c hc
  have hsum' : ∑ j, u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) = 1 := hsum
  choose ε U hU hUv using fun j => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.exists_form_of_mem_chartRingZ y c hc (hu j)
  have hle : ∀ j k, ε j k ≤ ∑ i, ε i k := fun j k =>
    Finset.single_le_sum (f := fun i => ε i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Dt : K → ℕ := fun k => ∑ i, ε i k with hDt
  set Φ : MRing ι := ∑ j, U j * G j * chartMon c (fun k => Dt k - ε j k) - chartMon c (fun k => Dt k + E k)
    with hΦ
  have hΦh : IsMultiHomog Φ (fun k => Dt k + E k) :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_sub (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_sum _ fun j _ => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_congr (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_mul (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_mul (hU j) (hG j)) (homog_chartMon c _))
      fun k => by
        have := hle j k
        simp only [Pi.add_apply, hDt] at this ⊢
        omega) (homog_chartMon c _)
  have key : ∀ j, (∏ k, y ⟨k, c k⟩ ^ ε j k) * (∏ k, y ⟨k, c k⟩ ^ L k) * (∏ k, y ⟨k, c k⟩ ^ (Dt k - ε j k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (Dt k + E k) := by
    intro j
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    have h1 := hE k
    have h2 : ε j k ≤ Dt k := hle j k
    push_cast [Nat.cast_sub h2]
    linarith
  have hΦy : aeval y Φ = 0 := by

    rw [hΦ, map_sub, map_sum, aeval_chartMon, sub_eq_zero]
    calc ∑ j, aeval y (U j * G j * chartMon c (fun k => Dt k - ε j k))
        = ∑ j, u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (Dt k + E k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, map_mul, hUv j, hGy j, aeval_chartMon]
          calc (u j * ∏ k, y ⟨k, c k⟩ ^ ε j k) * (v j * ∏ k, y ⟨k, c k⟩ ^ L k) *
                ∏ k, y ⟨k, c k⟩ ^ (Dt k - ε j k)
              = u j * v j * ((∏ k, y ⟨k, c k⟩ ^ ε j k) * (∏ k, y ⟨k, c k⟩ ^ L k) *
                  ∏ k, y ⟨k, c k⟩ ^ (Dt k - ε j k)) := by ring
            _ = _ := by rw [key j]; ring
      _ = ∏ k, y ⟨k, c k⟩ ^ (Dt k + E k) := by rw [← Finset.sum_mul, hsum', one_mul]
  have hΦx := hx.2 Φ (mem_of_homog hΦh hΦy)
  by_contra hall
  simp only [not_exists, not_not] at hall

  simp only [hΦ, map_sub, map_sum, map_mul, eval_chartMon, hall, mul_zero, zero_mul, Finset.sum_const_zero,
  zero_sub, neg_eq_zero] at hΦx
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hxc k)) hΦx

def substForms {N : ℕ} (G : Fin N → MRing ι) : (Σ k, addIdx ι N k) → MRing ι
  | ⟨none, j⟩ => G j
  | ⟨some k, i⟩ => X ⟨k, i⟩

theorem vanish_new {N : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin N → Ω) (E : K → ℕ) (ρ : Ω) (G : Fin N → MRing ι)
    (hG : ∀ j, IsMultiHomog (G j) E) (hGy : ∀ j, aeval y (G j) = v j * ρ)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) {f : MRing (addIdx ι N)}
    (hf : f ∈ mCoordIdeal (addBlock y v)) :
    eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) f) = 0 := by
  classical

  let Γ : MRing (addIdx ι N) →ₐ[ℤ] MvPolynomial (Option K) (MRing ι) :=
    aeval fun p => MvPolynomial.C (substForms G p) * MvPolynomial.X p.1

  let Θ : MvPolynomial (Option K) Ω →+* MvPolynomial (Option K) (MvPolynomial K Ω) :=
    eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun o => Option.elim o
      (MvPolynomial.C (MvPolynomial.C ρ * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ E k) * MvPolynomial.X none)
      fun k => MvPolynomial.C (MvPolynomial.X k) * MvPolynomial.X (some k)
  have hcomm : (MvPolynomial.map (mConeMap y).toRingHom).comp Γ.toRingHom =
      Θ.comp (mConeMap (addBlock y v)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int
        (((MvPolynomial.map (mConeMap y).toRingHom).comp Γ.toRingHom).comp C)
        ((Θ.comp (mConeMap (addBlock y v)).toRingHom).comp C)) r
    · obtain ⟨o, i⟩ := p
      cases o with
      | none =>
        change Fin N at i
        have hΓ : Γ (X ⟨none, i⟩) = MvPolynomial.C (G i) * MvPolynomial.X none := by
          simp only [Γ, aeval_X]
          rfl
        have hM : mConeMap (addBlock y v) (X ⟨none, i⟩) = MvPolynomial.C (v i) * MvPolynomial.X none := by
          simp only [mConeMap, aeval_X]
          rfl
        show MvPolynomial.map (mConeMap y).toRingHom (Γ (X ⟨none, i⟩)) = Θ (mConeMap (addBlock y v) (X ⟨none, i⟩))
        rw [hΓ, hM, map_mul, map_C, map_X, map_mul]
        have hC : ∀ w : Ω, Θ (MvPolynomial.C w) = MvPolynomial.C (MvPolynomial.C w) := fun w => eval₂Hom_C _ _ _
        have hX : Θ (MvPolynomial.X none) = MvPolynomial.C (MvPolynomial.C ρ *
            ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ E k) * MvPolynomial.X none := eval₂Hom_X' _ _ _
        rw [hC, hX, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog y (hG i), hGy i]
        simp only [map_mul]
        ring
      | some k =>
        have hΓ : Γ (X ⟨some k, i⟩) = MvPolynomial.C (X ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [Γ, aeval_X]
          rfl
        have hM : mConeMap (addBlock y v) (X ⟨some k, i⟩) = MvPolynomial.C (y ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [mConeMap, aeval_X]
          rfl
        show MvPolynomial.map (mConeMap y).toRingHom (Γ (X ⟨some k, i⟩)) =
          Θ (mConeMap (addBlock y v) (X ⟨some k, i⟩))
        rw [hΓ, hM, map_mul, map_C, map_X, map_mul]
        have hC : Θ (MvPolynomial.C (y ⟨k, i⟩)) = MvPolynomial.C (MvPolynomial.C (y ⟨k, i⟩)) := eval₂Hom_C _ _ _
        have hX : Θ (MvPolynomial.X (some k)) = MvPolynomial.C (MvPolynomial.X k) * MvPolynomial.X (some k) :=
          eval₂Hom_X' _ _ _
        have hY : (mConeMap y).toRingHom (X ⟨k, i⟩) = MvPolynomial.C (y ⟨k, i⟩) * MvPolynomial.X k := by
          simp [mConeMap]
        rw [hC, hX, hY, C_mul]
        ring
  have hzero : MvPolynomial.map (mConeMap y).toRingHom (Γ f) = 0 := by
    have h1 : MvPolynomial.map (mConeMap y).toRingHom (Γ f) = Θ (mConeMap (addBlock y v) f) :=
      RingHom.congr_fun hcomm f
    have h2 : mConeMap (addBlock y v) f = 0 := RingHom.mem_ker.mp hf
    rw [h1, h2, map_zero]

  let ψ : MRing ι →+* ℂ := (eval x).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hcoef : MvPolynomial.map ψ (Γ f) = 0 := by
    ext μ
    simp only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    have hm : AddMonoidAlgebra.coeff (Γ f) μ ∈ mCoordIdeal y := by
      show _ ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker]
      have := congrArg (AddMonoidAlgebra.coeff · μ) hzero
      simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using this
    exact hx.2 _ hm

  have hval : ((eval fun _ => (1 : ℂ)).comp ((MvPolynomial.map ψ).comp Γ.toRingHom)) =
      (eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)))).comp
        (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int
        (((eval fun _ => (1 : ℂ)).comp ((MvPolynomial.map ψ).comp Γ.toRingHom)).comp C)
        (((eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)))).comp
          (MvPolynomial.map (Int.castRingHom ℂ))).comp C)) r
    · obtain ⟨o, i⟩ := p
      cases o with
      | none =>
        change Fin N at i
        have hΓ : Γ (X ⟨none, i⟩) = MvPolynomial.C (G i) * MvPolynomial.X none := by
          simp only [Γ, aeval_X]
          rfl
        show eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ (X ⟨none, i⟩))) =
          eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) (X ⟨none, i⟩))
        rw [hΓ, map_mul, map_C, map_X, map_X, eval_X, map_mul, eval_C, eval_X, mul_one]
        rfl
      | some k =>
        have hΓ : Γ (X ⟨some k, i⟩) = MvPolynomial.C (X ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [Γ, aeval_X]
          rfl
        show eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ (X ⟨some k, i⟩))) =
          eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) (X ⟨some k, i⟩))
        rw [hΓ, map_mul, map_C, map_X, map_X, eval_X, map_mul, eval_C, eval_X, mul_one]
        simp [ψ]
        rfl
  have h3 : eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ f)) =
      eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) f) :=
    RingHom.congr_fun hval f
  rw [← h3, hcoef, map_zero]

end PowerBlockOldPartSurj

open PowerBlockOldPartSurj in
theorem PowerBlockOldPartSurj.proof : PowerBlockOldPartSurj.Statement := by
  intro K _ ι _ Ω _ y a m N v hv hgen x hx
  classical
  obtain ⟨c, hxc, hyc⟩ := exists_chart_at hx
  obtain ⟨L, E, G, hG, hE, hGy⟩ := exists_common_forms y c hyc a m N v hv
  obtain ⟨j, hj⟩ := exists_ne_zero hyc hgen hG hE hGy hx hxc
  refine ⟨addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)), ⟨fun k => ?_, fun f hf => ?_⟩, rfl⟩
  · cases k with
    | none => exact ⟨j, hj⟩
    | some k => exact ⟨c k, hxc k⟩
  · exact vanish_new y v E _ G hG hGy hx hf

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
