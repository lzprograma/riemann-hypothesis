module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionFormsTools
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.TypeStar
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleForms

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor

noncomputable section

set_option linter.unusedSectionVars false

namespace SegreFlagCutForms

open FlagBundleSectionForms (chartPow chartPow_ne_zero)

section Dual

variable {R : Type} [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N : ℕ} {E : Type} [AddCommGroup E]
  [Module Ω E]

theorem exists_flag_dual (y : (Σ k, ι k) → Ω) (B : ChartBundle R (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b)
    (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing R (segreVec y) c) ∧
      (∀ j, j < i → ψ (w j) = 0) ∧ ψ (w i) = (chartPow y c (b i))⁻¹ :=
  FlagBundleSectionForms.exists_flag_dual_of_frame y B w b hfl c hc i

end Dual

section Avoid

theorem exists_pair_not_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Infinite R]
    (G : Set (A × A)) (h0 : (0 : A × A) ∈ G) (hG : ∀ p ∈ G, ∀ q ∈ G, ∀ t : R, p + t • q ∈ G)
    (T : Finset (Ideal A))
    (hT : ∀ Q ∈ T, Q.IsPrime ∧ (∀ a : R, algebraMap R A a ∈ Q → a = 0) ∧ ∃ p ∈ G, p.2 ∉ Q) :
    ∃ p ∈ G, ∀ Q ∈ T, p.2 ∉ Q := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, h0, by simp⟩
  | @insert Q₀ T _ ih =>
    obtain ⟨x, hx, hxT⟩ := ih fun Q h => hT Q (Finset.mem_insert_of_mem h)
    obtain ⟨hQ₀, hC₀, y, hy, hyQ₀⟩ := hT Q₀ (Finset.mem_insert_self _ _)
    have hsub : ∀ Q ∈ T, {t : R | x.2 + algebraMap R A t * y.2 ∈ Q}.Subsingleton := by
      intro Q hQT t ht t' ht'
      obtain ⟨hQ, hCQ, -⟩ := hT Q (Finset.mem_insert_of_mem hQT)
      have hd : algebraMap R A (t - t') * y.2 ∈ Q := by
        have h := Q.sub_mem ht ht'
        rw [map_sub]
        convert h using 1
        ring
      rcases hQ.mem_or_mem hd with h | h
      · exact sub_eq_zero.mp (hCQ _ h)
      · exact absurd (by simpa using Q.sub_mem ht (Q.mul_mem_left (algebraMap R A t) h)) (hxT Q hQT)
    have hfin : (insert 0 (⋃ Q ∈ T, {t : R | x.2 + algebraMap R A t * y.2 ∈ Q})).Finite :=
      (T.finite_toSet.biUnion fun Q hQ => (hsub Q hQ).finite).insert 0
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset hfin.toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_iUnion, Set.mem_setOf_eq,
      not_or, not_exists] at ht
    obtain ⟨ht0, htT⟩ := ht
    have hsnd : (x + t • y).2 = x.2 + algebraMap R A t * y.2 := by
      rw [Prod.snd_add, Prod.smul_snd, Algebra.smul_def]
    by_cases hxQ₀ : x.2 ∈ Q₀
    · refine ⟨x + t • y, hG x hx y hy t, fun Q hQ => ?_⟩
      rw [hsnd]
      rcases Finset.mem_insert.mp hQ with rfl | hQT
      · intro h
        have h' : algebraMap R A t * y.2 ∈ Q := by simpa using Q.sub_mem h hxQ₀
        rcases hQ₀.mem_or_mem h' with h'' | h''
        · exact ht0 (hC₀ _ h'')
        · exact hyQ₀ h''
      · exact htT Q hQT
    · refine ⟨x, hx, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQT
      · exact hxQ₀
      · exact hxT Q hQT

end Avoid

section Flag

variable {Ω : Type} [Field Ω] {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem genVal_flag (w w' e : Module.Basis (Fin N) Ω E) (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0)
    (t : Fin N → Φ) (k : ℕ) (hk : k < N) (χ : Module.Dual Ω E)
    (hlow : ∀ j, j < (⟨k, hk⟩ : Fin N) → χ (w' j) = 0) (htop : χ (w' ⟨k, hk⟩) = 1) :
    genVal w (flagCoord w e t (k + 1)) χ = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ := by
  unfold genVal flagLineCoord
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) < k + 1
  · have hχ : χ (w j) = w'.repr (w j) ⟨k, hk⟩ := by
      conv_lhs => rw [← w'.sum_repr (w j)]

      rw [map_sum, Finset.sum_eq_single ⟨k, hk⟩]
      · rw [map_smul, htop, smul_eq_mul, mul_one]
      · intro m _ hm
        rcases lt_or_gt_of_ne hm with hlt | hgt
        · rw [map_smul, hlow m hlt, smul_zero]
        · have hjm : j < m := by
            rw [Fin.lt_def] at hgt ⊢
            simp only at hgt
            omega
          rw [repr_flag_inv w w' hsame j m hjm, zero_smul, map_zero]
      · simp
    rw [hχ]
  · have h0 : flagCoord w e t (k + 1) j = 0 := by
      unfold flagCoord
      rw [ite_eq_right hj]
    rw [h0, zero_mul, zero_mul]

theorem flagLineCoord_ne_zero (w w' e : Module.Basis (Fin N) Ω E)
    (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) (t : Fin N → Φ) (ht : AlgebraicIndependent Ω t)
    (k : ℕ) (hk : k < N) : flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ ≠ 0 := by
  intro h0
  have h1 := flagLineCoord_flag w w' e hsame t k hk
  rw [h0, mul_zero] at h1
  have h2 : flagLineCoord w w e t (k + 1) ⟨k, hk⟩ = ∑ i, w.repr (e i) ⟨k, hk⟩ • t i := by
    unfold flagLineCoord
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · rw [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, mul_one]
      unfold flagCoord
      rw [ite_eq_left (Nat.lt_succ_self k)]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    · intro j _ hj
      rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hj, map_zero, mul_zero]
    · simp
  rw [h2] at h1
  have hz := Fintype.linearIndependent_iff.mp ht.linearIndependent _ h1
  have hc : w.coord ⟨k, hk⟩ = 0 := e.ext fun i => by simpa using hz i
  have := congrArg (fun f => f (w ⟨k, hk⟩)) hc
  simp at this

end Flag

section Chart

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

theorem chart_pair (y : (Σ k, ι k) → Ω) (B' : ChartBundle O (segreVec y) N E)
    (w w' e : Module.Basis (Fin N) Ω E) (x' : Fin N → K → ℤ) (hfl' : IsFlagFrame y B' w' x')
    (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) (a₀' : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (hφ' : IsTwistedDualGens y B' a₀' φ')
    (t : Fin N → Φ) (k : ℕ) (hk : k < N) (c : ∀ k, ι k) :
    ∃ bH : K → ℕ, segreVec y c ≠ 0 → ∀ β : K → ℕ, (∀ j, bH j ≤ β j) →
      ∃ s : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsMultiHomog s (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat)) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ *
            aeval (flagClosurePt y w e φ φ' t (k + 1)) (chartMonoZ O M M' c β) := by
  by_cases hc : segreVec y c = 0
  · exact ⟨0, fun h => absurd hc h⟩
  have hY : ∀ j, y ⟨j, c j⟩ ≠ 0 := fun j => (Finset.prod_ne_zero_iff.1 hc) j (Finset.mem_univ _)
  obtain ⟨ψ, hψint, hψlow, hψk⟩ := exists_flag_dual y B' w' x' hfl' c hc ⟨k, hk⟩
  obtain ⟨u, hu, hψ⟩ := hφ'.generate c hc ψ hψint
  have hp := chartPow_ne_zero hY (x' ⟨k, hk⟩)
  have hexpr : algebraMap O Ω 1 ^ 0 • (chartPow y c (x' ⟨k, hk⟩) • ψ) =
      ∑ l, (u l * ∏ j, y ⟨j, c j⟩ ^ (x' ⟨k, hk⟩ j - a₀' j)) • φ' l := by
    rw [pow_zero, one_smul, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    have hsplit : ∏ j, y ⟨j, c j⟩ ^ (x' ⟨k, hk⟩ j - a₀' j) =
        chartPow y c (x' ⟨k, hk⟩) * ∏ j, y ⟨j, c j⟩ ^ (-a₀' j) := by
      unfold chartPow
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [sub_eq_add_neg, zpow_add₀ (hY j)]
    rw [hsplit]
    ring
  obtain ⟨bG, bH, G, hG, hdeg, hval⟩ := express_forms (M := M) (M' := M') y w φ φ'
    (flagCoord w e t (k + 1)) c hc (1 : O) φ' (chartPow y c (x' ⟨k, hk⟩) • ψ) a₀' (x' ⟨k, hk⟩) 0 u hu hexpr
  have hgen : genVal w (flagCoord w e t (k + 1)) (chartPow y c (x' ⟨k, hk⟩) • ψ) =
      flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ := by
    refine genVal_flag w w' e hsame t k hk _ (fun j hj => ?_) ?_
    · rw [LinearMap.smul_apply, hψlow j hj, smul_zero]
    · rw [LinearMap.smul_apply, hψk, smul_eq_mul, mul_inv_cancel₀ hp]
  rw [hgen] at hval
  simp only [pow_zero, map_one, one_mul] at hval
  refine ⟨bH, fun _ β hβ => ⟨(∑ l, X ⟨none, l⟩ * G l) * chartMonoZ O M M' c (β - bH), ?_, ?_⟩⟩
  · have h1 : IsMultiHomog (∑ l, X ⟨none, l⟩ * G l : MRing (bundleIdx (bundleIdx ι M) M') O)
        (Pi.single none 1 + vdeg bG) :=
      IsWeightedHomogeneous.sum _ _ _ fun l _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)
    have h2 := IsWeightedHomogeneous.mul h1 (chartMonoZ_homog (O := O) (M := M) (M' := M') c (β - bH))
    have hd : (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat) :
        Option (Option K) → ℕ) = Pi.single none 1 + vdeg bG + vdeg (β - bH) := by
      funext o
      rcases o with _ | _ | j
      · simp [vdeg]
      · simp [vdeg]
      · have h3 := hdeg j
        have h4 := hβ j
        simp [vdeg]
        omega
    rw [hd]
    exact h2
  · have hpt : flagClosurePt y w e φ φ' t (k + 1) = pairProjCoord y w φ φ' (flagCoord w e t (k + 1)) := rfl
    have hm : chartMonoZ O M M' c β = chartMonoZ O M M' c bH * chartMonoZ O M M' c (β - bH) := by
      unfold chartMonoZ
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← pow_add]
      congr 1
      have := hβ j
      simp only [Pi.sub_apply]
      omega
    have hs : aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1)))
        (∑ l, X ⟨none, l⟩ * G l : MRing (bundleIdx (bundleIdx ι M) M') O) =
        ∑ l, aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (G l) *
          genVal w (flagCoord w e t (k + 1)) (φ' l) := by

      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, aeval_X, mul_comm]; rfl
    rw [hpt, map_mul, hs, ← hval, hm, map_mul]
    ring

end Chart

end SegreFlagCutForms


open SegreFlagCutForms in
theorem SegreFlagCutForms.proof : SegreFlagCutForms.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk S hS
  classical
  have hInf : Infinite O :=
    Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)
  have hpt : flagClosurePt y w e φ φ' t (k + 1) = pairProjCoord y w φ φ' (flagCoord w e t (k + 1)) := rfl
  choose bH hbH using chart_pair (M := M) y B' w w' e x' hfl.flag' hfl.sameFlag a₀' φ φ' hφ' t k hk
  obtain ⟨β, hβ, hβD⟩ : ∃ β : K → ℕ, (∀ c j, bH c j ≤ β j) ∧ ∀ j, 0 ≤ (β j : ℤ) + (x' ⟨k, hk⟩ j - a₀' j) := by
    refine ⟨fun j => ∑ c, bH c j + (-(x' ⟨k, hk⟩ j - a₀' j)).toNat, fun c j => ?_, fun j => ?_⟩
    · exact le_trans (Finset.single_le_sum (f := fun c => bH c j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)) (Nat.le_add_right _ _)
    · have h1 := Int.self_le_toNat (-(x' ⟨k, hk⟩ j - a₀' j))
      have h2 : ((-(x' ⟨k, hk⟩ j - a₀' j)).toNat : ℤ) ≤
          ((∑ c, bH c j + (-(x' ⟨k, hk⟩ j - a₀' j)).toNat : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_add_left _ _
      beta_reduce
      omega
  set P := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hPdef
  set τ := flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ with hτdef
  set pt := flagClosurePt y w e φ φ' t (k + 1) with hptdef
  let G : Set (MRing (bundleIdx (bundleIdx ι M) M') O × MRing (bundleIdx (bundleIdx ι M) M') O) :=
    {p | IsMultiHomog p.1 (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat)) ∧
      IsMultiHomog p.2 (vdeg β) ∧ aeval pt p.1 = τ * aeval pt p.2}
  have h0 : (0 : MRing (bundleIdx (bundleIdx ι M) M') O × MRing (bundleIdx (bundleIdx ι M) M') O) ∈ G :=
    ⟨isWeightedHomogeneous_zero _ _ _, isWeightedHomogeneous_zero _ _ _, by simp⟩
  have hG : ∀ p ∈ G, ∀ q ∈ G, ∀ r : O, p + r • q ∈ G := by
    intro p hp q hq r
    refine ⟨?_, ?_, ?_⟩
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (add_mem
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp.1)
        (Submodule.smul_mem _ r ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hq.1)))
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (add_mem
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp.2.1)
        (Submodule.smul_mem _ r ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hq.2.1)))
    · show aeval pt (p.1 + r • q.1) = τ * aeval pt (p.2 + r • q.2)
      rw [map_add (f := _), map_add (f := _), map_smul, map_smul, hp.2.2, hq.2.2, mul_add, mul_smul_comm]

  have hpair : ∀ (Q : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) (c : ∀ j, ι j),
      segreVec y c ≠ 0 → chartMonoZ O M M' c β ∉ Q → ∃ p ∈ G, p.2 ∉ Q := by
    intro Q c hc hcQ
    obtain ⟨s, hs, hsv⟩ := hbH c hc β (hβ c)
    exact ⟨(s, chartMonoZ O M M' c β), ⟨hs, chartMonoZ_homog c β, hsv⟩, hcQ⟩
  have hT : ∀ Q ∈ insert P S, Q.IsPrime ∧
      (∀ a : O, algebraMap O (MRing (bundleIdx (bundleIdx ι M) M') O) a ∈ Q → a = 0) ∧ ∃ p ∈ G, p.2 ∉ Q := by
    intro Q hQ
    rw [MvPolynomial.algebraMap_eq]
    rcases Finset.mem_insert.mp hQ with rfl | hQS
    · refine ⟨RingHom.ker_isPrime _, fun a ha => ?_, ?_⟩
      · have h1 : aeval pt (C a : MRing (bundleIdx (bundleIdx ι M) M') O) = 0 := aeval_eq_zero_of_mem ha
        rw [aeval_C, IsScalarTower.algebraMap_apply O Ω Φ] at h1
        have h2 : algebraMap O Ω a = 0 := (algebraMap Ω Φ).injective (by rw [h1, map_zero])
        have h3 : (C a : MRing ι O) ∈ pointIdeal O y :=
          mem_of_homog (b := 0) (isWeightedHomogeneous_C _ _) (by rw [aeval_C, h2])
        have h4 : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := h3
        rw [hV.noTorsion] at h4
        exact (Submodule.mem_bot O).mp h4
      · choose c hc using hV.multiProj.relevant
        have hY : ∀ j, y ⟨j, c j⟩ ≠ 0 := fun j h0 =>
          hc j (mem_of_homog (isWeightedHomogeneous_X O _ _) (by rw [aeval_X, h0]))
        refine hpair _ c (Finset.prod_ne_zero_iff.mpr fun j _ => hY j) fun hm => ?_
        have h1 := aeval_eq_zero_of_mem hm
        change aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (chartMonoZ O M M' c β) = 0 at h1
        rw [aeval_chartMonoZ] at h1
        exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hY j))
          ((map_eq_zero_iff _ (algebraMap Ω Φ).injective).mp h1)
    · obtain ⟨hQp, hQr, hPQ, hϖQ⟩ := hS Q hQS
      refine ⟨hQp, fun a ha => ?_, ?_⟩
      · by_contra ha0
        obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
        rw [map_mul, map_pow] at ha
        rcases hQp.mem_or_mem ha with h | h
        · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))
        · exact hϖQ (hQp.mem_of_pow_mem _ h)
      · choose c hc using fun j : K => hQr (some (some j))
        have nz : ∀ j, y ⟨j, c j⟩ ≠ 0 := by
          intro j h0
          refine hc j (hPQ (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))
          rw [aeval_X]
          show algebraMap Ω Φ (y ⟨j, c j⟩) = 0
          rw [h0, map_zero]
        refine hpair Q c (Finset.prod_ne_zero_iff.mpr fun j _ => nz j) fun hm => ?_
        obtain ⟨j, -, hj⟩ := hQp.prod_mem_iff.mp hm
        exact hc j (hQp.mem_of_pow_mem _ hj)
  obtain ⟨⟨s, h⟩, ⟨hs, hh, hval⟩, hav⟩ := exists_pair_not_mem (R := O) G h0 hG (insert P S) hT
  have hhP : h ∉ P := hav P (Finset.mem_insert_self _ _)
  have hτ : τ ≠ 0 := flagLineCoord_ne_zero w w' e hfl.sameFlag t ht k hk
  have hsP : s ∉ P := by
    intro hm
    have h1 := aeval_eq_zero_of_mem hm
    rw [hval] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hτ h2
    · exact hhP (mem_of_homog hh h2)
  refine ⟨_, _, s, h, hs, hh, ?_, hsP, hhP, hval, fun Q hQ => hav Q (Finset.mem_insert_of_mem hQ)⟩
  funext o
  rcases o with _ | _ | j
  · simp [vdeg, zetaSecond, liftPairDeg]
  · simp [vdeg, zetaSecond, liftPairDeg]
  · have := hβD j
    simp [vdeg, zetaSecond, liftPairDeg]
    omega

end

end GroundTheory.Heights₂.Heights.NumbersDVR
