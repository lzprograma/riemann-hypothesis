module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ClassSums
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal
import Mathlib.Data.Pi.Interval
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.OrbTrace

section Descent

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem exists_invariant [Finite (B ≃ₐ[A] B)] (𝔷 : Ideal B) (hz : 𝔷.IsMaximal) (E : ℕ) (F : B)
    (hF : ∀ σ : B ≃ₐ[A] B, 𝔷.comap σ = 𝔷 → σ F = F) :
    ∃ f : B, (∀ σ : B ≃ₐ[A] B, σ f = f) ∧ f - F ∈ 𝔷 ^ E := by
  classical
  have := Fintype.ofFinite (B ≃ₐ[A] B)
  have hD : ∀ σ : B ≃ₐ[A] B, 𝔷.comap σ = 𝔷 → ∀ b ∈ 𝔷 ^ E, σ b ∈ 𝔷 ^ E := fun σ hσ b hb ↦ by
    have : 𝔷 ^ E ≤ (𝔷 ^ E).comap σ := by
      conv_lhs => rw [← hσ]
      exact Ideal.le_comap_pow _ _
    exact this hb
  have hv : ∀ τ : B ≃ₐ[A] B, 𝔷.comap τ ≠ 𝔷 → ∃ v : B, v - 1 ∈ 𝔷 ^ E ∧ τ v ∈ 𝔷 ^ E := fun τ hτ ↦ by
    have hm : (𝔷.comap τ).IsMaximal := Ideal.comap_isMaximal_of_surjective τ τ.surjective
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 (Ideal.pow_sup_pow_eq_top (hm.coprime_of_ne hz hτ)))
    exact ⟨a, (show a - 1 = -b by rw [← hab]; ring) ▸ neg_mem hb, Ideal.le_comap_pow τ E ha⟩
  have hone : ∀ {ι : Type} (s : Finset ι) (v : ι → B), (∀ i ∈ s, v i - 1 ∈ 𝔷 ^ E) → ∏ i ∈ s, v i - 1 ∈ 𝔷 ^ E := fun s v h ↦ by
    rw [← Ideal.Quotient.eq, map_prod, map_one]
    exact Finset.prod_eq_one fun i hi ↦ by simpa using Ideal.Quotient.eq.2 (h i hi)
  choose! v hv1 hv2 using hv
  set u₀ : B := ∏ τ ∈ Finset.univ.filter (fun τ : B ≃ₐ[A] B ↦ 𝔷.comap τ ≠ 𝔷), v τ
  have hu1 : u₀ - 1 ∈ 𝔷 ^ E := hone _ _ fun τ hτ ↦ hv1 τ (Finset.mem_filter.1 hτ).2
  have hu2 : ∀ τ : B ≃ₐ[A] B, 𝔷.comap τ ≠ 𝔷 → τ u₀ ∈ 𝔷 ^ E := fun τ hτ ↦ by
    obtain ⟨w, hw⟩ : v τ ∣ u₀ := Finset.dvd_prod_of_mem _ (by simpa using hτ)
    rw [hw, map_mul]; exact Ideal.mul_mem_right _ _ (hv2 τ hτ)
  set D := Finset.univ.filter (fun τ : B ≃ₐ[A] B ↦ 𝔷.comap τ = 𝔷)
  have hmemD : ∀ τ : B ≃ₐ[A] B, 𝔷.comap τ = 𝔷 ↔ ∀ b, τ b ∈ 𝔷 ↔ b ∈ 𝔷 := fun τ ↦ by rw [Ideal.ext_iff]; rfl
  set u : B := ∏ δ ∈ D, δ u₀
  have hU1 : u - 1 ∈ 𝔷 ^ E := hone _ _ fun δ hδ ↦ by simpa using hD δ (Finset.mem_filter.1 hδ).2 _ hu1
  have hU2 : ∀ τ : B ≃ₐ[A] B, 𝔷.comap τ ≠ 𝔷 → τ u ∈ 𝔷 ^ E := fun τ hτ ↦ by
    obtain ⟨w, hw⟩ : (1 : B ≃ₐ[A] B) u₀ ∣ u := Finset.dvd_prod_of_mem _ (by simp [D, hmemD])
    rw [hw, map_mul]; exact Ideal.mul_mem_right _ _ (hu2 τ hτ)
  have hU3 : ∀ σ : B ≃ₐ[A] B, 𝔷.comap σ = 𝔷 → σ u = u := fun σ hσ ↦ by
    rw [map_prod]; refine Finset.prod_equiv (Equiv.mulLeft σ) (fun δ ↦ ?_) (fun _ _ ↦ rfl)
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, hmemD, Equiv.coe_mulLeft, AlgEquiv.mul_apply]
    rw [hmemD] at hσ; simp only [hσ]
  set x := u * F
  set T : Finset B := Finset.univ.image (fun σ : B ≃ₐ[A] B ↦ σ x)
  refine ⟨∑ b ∈ T, b, fun σ ↦ ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in rw [map_sum]
    refine Finset.sum_equiv σ.toEquiv (fun b ↦ ?_) (fun _ _ ↦ rfl)
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨by rintro ⟨τ, rfl⟩; exact ⟨σ * τ, rfl⟩,
      fun ⟨τ, hτ⟩ ↦ ⟨σ⁻¹ * τ, by rw [AlgEquiv.mul_apply, hτ]; exact σ.symm_apply_apply b⟩⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_image.2 ⟨1, Finset.mem_univ _, rfl⟩ : x ∈ T),
      show x + ∑ b ∈ T.erase x, b - F = (u - 1) * F + ∑ b ∈ T.erase x, b by ring]
    refine add_mem (Ideal.mul_mem_right _ _ hU1) (Ideal.sum_mem _ fun b hb ↦ ?_)
    obtain ⟨hne, hb⟩ := Finset.mem_erase.1 hb
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hb
    by_cases hτ : 𝔷.comap τ = 𝔷
    · exact absurd (by rw [map_mul, hU3 τ hτ, hF τ hτ]) hne
    · rw [map_mul]; exact Ideal.mul_mem_right _ _ (hU2 τ hτ)

theorem exists_pow_le [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A B] (𝔷 : Ideal B) (hz : 𝔷.IsMaximal) (e : ℕ) :
    ∃ E : ℕ, ∀ b ∈ 𝔷 ^ E, ∃ s, s ∉ 𝔷 ∧ s * b ∈ ((maximalIdeal A) ^ e).map (algebraMap A B) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let I := ((maximalIdeal A) ^ e).map (algebraMap A B)
  let J : Ideal B :=
    { carrier := {b | ∃ s, s ∉ 𝔷 ∧ s * b ∈ I}
      add_mem' := fun {a b} ⟨s, hs, ha⟩ ⟨t, ht, hb⟩ ↦ ⟨s * t, fun h ↦ (hz.isPrime.mem_or_mem h).elim hs ht,
        (show s * t * (a + b) = t * (s * a) + s * (t * b) by ring) ▸ add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)⟩
      zero_mem' := ⟨1, fun h ↦ hz.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
      smul_mem' := fun c {b} ⟨s, hs, hb⟩ ↦ ⟨s, hs,
        (show s * (c • b) = c * (s * b) by rw [smul_eq_mul]; ring) ▸ I.mul_mem_left _ hb⟩ }
  suffices h : 𝔷 ≤ J.radical from Ideal.exists_pow_le_of_le_radical_of_fg h (IsNoetherian.noetherian _)
  intro z hzz; by_contra hn
  have := hz.isPrime
  have hdis : Disjoint (I : Set B) ((𝔷.primeCompl ⊔ Submonoid.powers z : Submonoid B) : Set B) :=
    Set.disjoint_left.2 fun _ hwI hw ↦ by
      obtain ⟨s, hs, _, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.1 hw
      exact hn ⟨n, s, hs, hwI⟩
  obtain ⟨P, hP, hIP, hPd⟩ := Ideal.exists_le_prime_disjoint I _ hdis
  have hPz : P ≤ 𝔷 := fun _ hw ↦ by_contra fun h ↦ Set.disjoint_left.1 hPd hw (Submonoid.mem_sup_left h)
  have hm' : (P.comap (algebraMap A B)).IsMaximal := by
    rw [← (maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.IsPrime.le_of_pow_le (Ideal.map_le_iff_le_comap.1 hIP))]; infer_instance
  exact Set.disjoint_left.1 hPd ((Ideal.isMaximal_of_isIntegral_of_isMaximal_under P hm').eq_of_le hz.ne_top hPz ▸ hzz : z ∈ P)
    (Submonoid.mem_sup_right (Submonoid.mem_powers z))

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem exists_norm_le [IsNoetherianRing A] (m : Ideal A) (φ : B →+* K) (hφ : ∀ b, ‖φ b‖ ≤ 1) :
    ∃ h ∈ m, ∀ e : ℕ, ∀ b ∈ (m ^ e).map (algebraMap A B), ‖φ b‖ ≤ ‖φ (algebraMap A B h)‖ ^ e := by
  classical
  let ball : ℝ → Ideal B := fun r ↦
    { carrier := {b | ‖φ b‖ ≤ |r|}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun c {b} hb ↦ by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (hφ c)).trans hb }
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian m
  obtain ⟨h, hh, hmax⟩ := Finset.exists_max_image (insert 0 s) (fun a ↦ ‖φ (algebraMap A B a)‖) (Finset.insert_nonempty _ _)
  refine ⟨h, (Finset.mem_insert.1 hh).elim (fun e ↦ e ▸ zero_mem _) (fun hh ↦ hs ▸ Submodule.subset_span hh), fun e ↦ ?_⟩
  set r := ‖φ (algebraMap A B h)‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have h1 : m.map (algebraMap A B) ≤ ball r := by
    rw [Ideal.map_le_iff_le_comap, ← hs, Submodule.span_le]
    intro a ha; show ‖φ (algebraMap A B a)‖ ≤ |r|
    rw [abs_of_nonneg hr0]; exact hmax a (Finset.mem_insert_of_mem ha)
  have h2 : ∀ e : ℕ, (m.map (algebraMap A B)) ^ e ≤ ball (r ^ e) := fun e ↦ by
    induction e with
    | zero => intro b _; show ‖φ b‖ ≤ |r ^ 0|; simpa using hφ b
    | succ e ih =>
      rw [pow_succ, Ideal.mul_le]
      intro a ha b hb
      show ‖φ (a * b)‖ ≤ |r ^ e * r|
      rw [map_mul, norm_mul, abs_mul]
      exact mul_le_mul (ih ha) (h1 hb) (norm_nonneg _) (abs_nonneg _)
  intro b hb; rw [Ideal.map_pow] at hb
  have := h2 e hb; show ‖φ b‖ ≤ r ^ e; rwa [← abs_of_nonneg (pow_nonneg hr0 e)]

theorem norm_eq_one (𝔷 : Ideal B) (hz : 𝔷.IsMaximal) (φ : B →+* K) (hφ : ∀ b, ‖φ b‖ ≤ 1) (hφ' : ∀ b ∈ 𝔷, ‖φ b‖ < 1)
    (s : B) (hs : s ∉ 𝔷) : ‖φ s‖ = 1 := by
  obtain ⟨y, i, hi, h⟩ := hz.exists_inv hs
  by_contra hne
  have h1 : ‖φ (y * s + i)‖ = 1 := by rw [h]; simp
  rw [map_add (f := _), map_mul] at h1
  have h2 := IsUltrametricDist.norm_add_le_max (φ y * φ s) (φ i)
  have h3 : ‖φ y * φ s‖ < 1 := by
    rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hφ y)).trans_lt (lt_of_le_of_ne (hφ s) hne)
  linarith [max_lt h3 (hφ' i hi)]

theorem norm_prod_sub_le {ι : Type} (s : Finset ι) (a b : ι → K) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hab : ∀ i, ‖a i - b i‖ ≤ ε) : ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ε := by
  classical
  have hb : ∀ i, ‖b i‖ ≤ 1 := fun i ↦ by
    rw [show b i = a i + -(a i - b i) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (by rw [norm_neg]; exact (hab i).trans h1))
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj,
      show a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (ha j)).trans ih)
      (by rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _)
        (by rw [norm_prod]; exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hb i)).trans (hab j)))

end Descent

section Classes

variable {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {N : ℕ}

theorem cm_refl (x : X) : CongMod N x x := ⟨0, by simp⟩

theorem cm_symm {x y : X} (h : CongMod N x y) : CongMod N y x := by obtain ⟨w, rfl⟩ := h; exact ⟨-w, by simp⟩

theorem cm_trans {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h; obtain ⟨w', rfl⟩ := h'; exact ⟨w' + w, by rw [smul_add, add_assoc]⟩

theorem cm_map (γ : X →ₗ[ℤ] X') {x y : X} (h : CongMod N x y) : CongMod N (γ x) (γ y) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨γ w, by simp⟩

theorem cm_of_det [Module.Free ℤ X] [Module.Finite ℤ X] (γ : X →ₗ[ℤ] X) (hγ : (N : ℤ) ∣ LinearMap.det γ - 1) {x y : X}
    (h : CongMod N (γ x) (γ y)) : CongMod N x y := by
  classical
  let b := Module.finBasis ℤ X
  let δ : X →ₗ[ℤ] X := Matrix.toLin b b (LinearMap.toMatrix b b γ).adjugate
  have hδ : ∀ z, δ (γ z) = LinearMap.det γ • z := fun z ↦ by
    have : δ ∘ₗ γ = LinearMap.det γ • LinearMap.id := (LinearMap.toMatrix b b).injective (by
      rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_toLin, Matrix.adjugate_mul, LinearMap.det_toMatrix, map_smul,
        LinearMap.toMatrix_id])
    exact LinearMap.congr_fun this z
  obtain ⟨d, hd⟩ := hγ
  have h1 : ∀ z, CongMod N (δ (γ z)) z := fun z ↦ ⟨d • z, by
    rw [hδ, sub_eq_iff_eq_add'.1 hd, add_smul, one_smul, mul_smul, natCast_zsmul]⟩
  exact cm_trans (cm_symm (h1 x)) (cm_trans (cm_map δ h) (h1 y))

theorem exists_rep [Module.Free ℤ X] [Module.Finite ℤ X] (hN : 1 ≤ N) :
    ∃ r : X → X, (∀ x, CongMod N (r x) x) ∧ (∀ x y, CongMod N x y → r x = r y) ∧ (Set.range r).Finite := by
  let b := Module.finBasis ℤ X
  refine ⟨fun x ↦ b.equivFun.symm (fun i ↦ b.equivFun x i % N), fun x ↦ ?_, fun x y ⟨w, hw⟩ ↦ ?_, ?_⟩
  · refine ⟨b.equivFun.symm (fun i ↦ -(b.equivFun x i / N)), b.equivFun.injective ?_⟩
    ext i
    simp only [LinearEquiv.apply_symm_apply, map_add (f := _), map_nsmul, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    rw [Int.emod_def]; ring
  · subst hw; simp [Int.add_mul_emod_self_left]
  · refine ((Set.finite_Icc (fun _ ↦ (0 : ℤ)) (fun _ ↦ (N : ℤ))).image b.equivFun.symm).subset fun _ ⟨x, hx⟩ ↦ ?_
    have : (0 : ℤ) < N := by exact_mod_cast hN
    exact ⟨_, ⟨fun i ↦ Int.emod_nonneg _ this.ne', fun i ↦ (Int.emod_lt_of_pos _ this).le⟩, hx⟩

variable {O : Type} [CommRing O] [Module O X] [Module O X'] {N₁ : ℕ}

theorem exists_classes [Module.Free ℤ X] [Module.Finite ℤ X] (hN : 1 ≤ N) {ι : Type} [Fintype ι] (a : ι → X) :
    ∃ C : Finset (ι → X), (∀ c ∈ C, c ∈ orbit O N₁ N LinearMap.id a) ∧
      (∀ c ∈ C, ∀ c' ∈ C, (∀ i, CongMod N (c i) (c' i)) → c = c') ∧
      (∀ μ ∈ orbit O N₁ N LinearMap.id a, ∃ c ∈ C, ∀ i, CongMod N (c i) (μ i)) := by
  obtain ⟨r, h1, h2, h3⟩ := exists_rep (X := X) hN
  have hfin : {c : ι → X | (∀ i, r (c i) = c i) ∧ c ∈ orbit O N₁ N LinearMap.id a}.Finite :=
    (Set.Finite.pi' (fun _ : ι ↦ h3)).subset fun c hc i ↦ ⟨_, hc.1 i⟩
  refine ⟨hfin.toFinset, fun c hc ↦ (hfin.mem_toFinset.1 hc).2, fun c hc c' hc' h ↦ funext fun i ↦ ?_, fun μ hμ ↦ ?_⟩
  · rw [← (hfin.mem_toFinset.1 hc).1 i, ← (hfin.mem_toFinset.1 hc').1 i]; exact h2 _ _ (h i)
  · obtain ⟨γ, g1, g2, g3, g4⟩ := hμ
    exact ⟨fun i ↦ r (μ i), hfin.mem_toFinset.2 ⟨fun i ↦ h2 _ _ (h1 _), ⟨γ, g1, g2, g3, fun i ↦ cm_trans (h1 _) (g4 i)⟩⟩, fun i ↦ h1 _⟩

theorem comp_mem_orbit [Module.Free ℤ X] [Module.Finite ℤ X] {ι : Type} {a c : ι → X} (γ : X →ₗ[ℤ] X)
    (h1 : ∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) (h2 : (N : ℤ) ∣ LinearMap.det γ - 1) (h3 : ∀ x, CongMod N₁ (γ x) x)
    (hc : c ∈ orbit O N₁ N LinearMap.id a) : (fun i ↦ γ (c i)) ∈ orbit O N₁ N LinearMap.id a := by
  obtain ⟨δ, g1, g2, g3, g4⟩ := hc
  refine ⟨γ ∘ₗ δ, fun o x ↦ cm_trans (cm_map γ (g1 o x)) (h1 o _), ?_, fun x ↦ cm_trans (h3 _) (g3 x), fun i ↦ cm_map γ (g4 i)⟩
  rw [LinearMap.det_comp, show LinearMap.det γ * LinearMap.det δ - 1 = (LinearMap.det γ - 1) * LinearMap.det δ + (LinearMap.det δ - 1) by ring]
  exact dvd_add (h2.mul_right _) g2

theorem sum_comp_eq [Module.Free ℤ X] [Module.Finite ℤ X] {ι M : Type} [AddCommMonoid M] {a : ι → X} (C : Finset (ι → X))
    (hC1 : ∀ c ∈ C, c ∈ orbit O N₁ N LinearMap.id a) (hC2 : ∀ c ∈ C, ∀ c' ∈ C, (∀ i, CongMod N (c i) (c' i)) → c = c')
    (hC3 : ∀ μ ∈ orbit O N₁ N LinearMap.id a, ∃ c ∈ C, ∀ i, CongMod N (c i) (μ i)) (γ : X →ₗ[ℤ] X)
    (h1 : ∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) (h2 : (N : ℤ) ∣ LinearMap.det γ - 1) (h3 : ∀ x, CongMod N₁ (γ x) x)
    (g : (ι → X) → M) (hg : ∀ c c', (∀ i, CongMod N (c i) (c' i)) → g c = g c') :
    ∑ c ∈ C, g (fun i ↦ γ (c i)) = ∑ c ∈ C, g c := by
  choose! ρ hρ1 hρ2 using hC3
  have hm : ∀ c ∈ C, (fun i ↦ γ (c i)) ∈ orbit O N₁ N LinearMap.id a := fun c hc ↦ comp_mem_orbit γ h1 h2 h3 (hC1 c hc)
  have hmaps : Set.MapsTo (fun c : ι → X ↦ ρ (fun i ↦ γ (c i))) C C := fun c hc ↦ hρ1 _ (hm c hc)
  have hinj : Set.InjOn (fun c : ι → X ↦ ρ (fun i ↦ γ (c i))) C := fun c hc c' hc' h ↦
    hC2 c hc c' hc' fun i ↦ cm_of_det γ h2 (by
      have e1 := hρ2 _ (hm c hc) i
      simp only at h; rw [h] at e1
      exact cm_trans (cm_symm e1) (hρ2 _ (hm c' hc') i))
  exact Finset.sum_nbij _ hmaps hinj ((C.finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj).surjOn
    fun c hc ↦ (hg _ _ (hρ2 _ (hm c hc))).symm

open Classical in
theorem sum_orbit_eq [Module.Free ℤ X] [Module.Finite ℤ X] {m s : ℕ} {K : Type} [CommRing K] {a : Fin m × Fin s → X}
    (C : Finset (Fin m × Fin s → X))
    (hC1 : ∀ c ∈ C, c ∈ orbit O N₁ N LinearMap.id a) (hC2 : ∀ c ∈ C, ∀ c' ∈ C, (∀ i, CongMod N (c i) (c' i)) → c = c')
    (hC3 : ∀ μ ∈ orbit O N₁ N LinearMap.id a, ∃ c ∈ C, ∀ i, CongMod N (c i) (μ i)) (k : X →ₗ[ℤ] X')
    (hk : IsUnimodMod O N k) (T : Finset (Fin s → X')) (S : Finset (Fin m × Fin s → X'))
    (hS : ∀ μ, μ ∈ S ↔ μ ∈ orbit O N₁ N k a ∧ ∀ i, (fun u ↦ μ (i, u)) ∈ T) (t : Fin m → (Fin s → X') → K) :
    ∑ μ ∈ S, ∏ i, t i (fun u ↦ μ (i, u)) =
      ∑ c ∈ C, ∏ i, ∑ ν ∈ T.filter (fun ν ↦ ∀ u, CongMod N (ν u) (k (c (i, u)))), t i ν := by
  have hinj : ∀ x y, CongMod N (k x) (k y) → CongMod N x y := by
    obtain ⟨-, ε, hε⟩ := hk; exact fun x y h ↦ cm_of_det _ hε (cm_map ε.toLinearMap h)
  have step : ∀ c ∈ C, ∏ i, ∑ ν ∈ T.filter (fun ν ↦ ∀ u, CongMod N (ν u) (k (c (i, u)))), t i ν =
      ∑ μ ∈ S, if (∀ j, CongMod N (μ j) (k (c j))) then ∏ i, t i (fun u ↦ μ (i, u)) else 0 := fun c hc ↦ by
    rw [Finset.prod_univ_sum, ← Finset.sum_filter]; symm
    refine Finset.sum_bij' (fun μ _ i u ↦ μ (i, u)) (fun x _ j ↦ x j.1 j.2)
      (fun μ hμ ↦ Fintype.mem_piFinset.2 fun i ↦ Finset.mem_filter.2 ⟨((hS μ).1 (Finset.mem_filter.1 hμ).1).2 i,
        fun u ↦ (Finset.mem_filter.1 hμ).2 _⟩)
      (fun x hx ↦ by
        have hx' := fun i ↦ Finset.mem_filter.1 (Fintype.mem_piFinset.1 hx i)
        obtain ⟨γ, g1, g2, g3, g4⟩ := hC1 c hc
        exact Finset.mem_filter.2 ⟨(hS _).2 ⟨⟨γ, g1, g2, g3, fun j ↦ cm_trans ((hx' j.1).2 j.2) (cm_map k (g4 j))⟩,
          fun i ↦ (hx' i).1⟩, fun j ↦ (hx' j.1).2 j.2⟩)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  obtain ⟨γ, g1, g2, g3, g4⟩ := ((hS μ).1 hμ).1
  obtain ⟨c, hc, hc'⟩ := hC3 (fun j ↦ γ (a j)) ⟨γ, g1, g2, g3, fun j ↦ cm_refl _⟩
  have hμc : ∀ j, CongMod N (μ j) (k (c j)) := fun j ↦ cm_trans (g4 j) (cm_map k (cm_symm (hc' j)))
  rw [Finset.sum_eq_single_of_mem c hc, ite_eq_left hμc]
  intro c' hc'' hne; rw [ite_eq_right]; intro h
  exact hne (hC2 _ hc'' _ hc fun j ↦ hinj _ _ (cm_trans (cm_symm (h j)) (hμc j)))

end Classes

theorem orbitSums_of_classSums : ∀ (O : Type) [CommRing O] (bar : O → O) (q p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (Φ : FPre bar q p A) (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)], Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → ∀ 𝔷 : Ideal B, 𝔷.IsMaximal → 1 ≤ N → PosW W → (∀ y, IsUnimodMod O N (k y)) → Φ.ClassSums N₁ N y₀ k t B 𝔷 → Φ.OrbitSums W N₁ N y₀ k t := by
  intro O _ bar q p _ A _ _ _ _ _ Φ s W N₁ N y₀ k Q t B _ _ _ _ _ _ hfix 𝔷 hz hN hW hk hcs m a κ e
  classical
  obtain ⟨ev', f, hev, hle, hlt, hf, hsum, hγ⟩ := hcs
  obtain ⟨C, hC1, hC2, hC3⟩ := exists_classes (O := O) (N₁ := N₁) hN a
  obtain ⟨E, hE⟩ := exists_pow_le (A := A) 𝔷 hz e
  set F : B := ∑ c ∈ C, ∏ i, f (fun u ↦ c (i, u)) (κ i)
  obtain ⟨g, hg1, hg2⟩ := exists_invariant (A := A) 𝔷 hz E F fun σ hσ ↦ by
    obtain ⟨γ, h1, h2, h3, h4⟩ := hγ σ hσ
    rw [map_sum]; simp only [map_prod, h4]
    exact sum_comp_eq C hC1 hC2 hC3 γ h1 h2 h3 (fun c ↦ ∏ i, f (fun u ↦ c (i, u)) (κ i))
      fun c c' h ↦ Finset.prod_congr rfl fun i _ ↦ hf _ _ _ fun u ↦ h _
  obtain ⟨g₀, rfl⟩ := hfix g hg1
  obtain ⟨σ, hσ, hσ'⟩ := hE _ hg2
  refine ⟨g₀, fun y ↦ ?_⟩
  obtain ⟨h, hh, hb⟩ := exists_norm_le (maximalIdeal A) (ev' y) (hle y)
  refine ⟨h, hh, fun ε hε ↦ ?_⟩
  have hgF : ‖Φ.ev y g₀ - ev' y F‖ ≤ ‖Φ.ev y h‖ ^ e := by
    have := hb e _ hσ'
    rwa [map_mul, norm_mul, norm_eq_one 𝔷 hz _ (hle y) (hlt y) σ hσ, one_mul, map_sub, hev, hev] at this
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  choose S₀ hS₀ using fun c κ ↦ hsum y c κ _ hε'
  obtain ⟨c₀, hc₀, hq⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W hW
  have hβ0 : ∀ x, 0 ≤ Φ.β y x x := fun x ↦ by
    by_cases hx : x = 0
    · simp [hx]
    · exact (Φ.pos y x hx).le
  have hq' := hq _ (Φ.β y) (Φ.bal y).1 hβ0
  have hq0 : ∀ ν : Fin s → Φ.X y, (0 : ℝ) ≤ (qW W (Φ.β y) ν : ℤ) := fun ν ↦
    le_trans (mul_nonneg hc₀.le (by exact_mod_cast Finset.sum_nonneg fun u _ ↦ hβ0 _)) (hq' ν)
  have hsc := Φ.sc_pos y
  set R : ℝ := -Real.log ε / Φ.sc y
  have hT₁ : {ν : Fin s → Φ.X y | ((qW W (Φ.β y) ν : ℤ) : ℝ) ≤ R}.Finite :=
    (Set.Finite.pi' (fun _ : Fin s ↦ GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite _ (Φ.β y) (Φ.bal y).1 (Φ.pos y) ⌈R / c₀⌉)).subset
      fun ν hν u ↦ by exact_mod_cast ((show ((Φ.β y (ν u) (ν u) : ℤ) : ℝ) ≤ ((∑ u, Φ.β y (ν u) (ν u) : ℤ) : ℝ) by
        exact_mod_cast Finset.single_le_sum (f := fun u ↦ Φ.β y (ν u) (ν u)) (fun u _ ↦ hβ0 _) (Finset.mem_univ u)).trans
        ((le_div_iff₀' hc₀).2 ((hq' ν).trans hν))).trans (Int.le_ceil _)
  set T : Finset (Fin s → Φ.X y) := hT₁.toFinset ∪ C.biUnion fun c ↦ Finset.univ.biUnion fun i ↦ S₀ (fun u ↦ c (i, u)) (κ i)
  have hSfin : {μ : Fin m × Fin s → Φ.X y | μ ∈ orbit O N₁ N (k y) a ∧ ∀ i, (fun u ↦ μ (i, u)) ∈ T}.Finite :=
    ((Set.Finite.pi' (fun _ : Fin m ↦ T.finite_toSet)).image (fun x j ↦ x j.1 j.2)).subset fun μ hμ ↦ ⟨fun i u ↦ μ (i, u), hμ.2, rfl⟩
  refine ⟨hSfin.toFinset, fun μ hμ ↦ (hSfin.mem_toFinset.1 hμ).1, fun μ hμ hμS ↦ ?_, ?_⟩
  · rw [hSfin.mem_toFinset] at hμS
    obtain ⟨i, hi⟩ : ∃ i, (fun u ↦ μ (i, u)) ∉ T := by by_contra! hcon; exact hμS ⟨hμ, hcon⟩
    have h1 : R < ((qW W (Φ.β y) (fun u ↦ μ (i, u)) : ℤ) : ℝ) := by
      by_contra hcon; exact hi (Finset.mem_union_left _ (hT₁.mem_toFinset.2 (not_lt.1 hcon)))
    have h2 := h1.trans_le (Finset.single_le_sum (f := fun i ↦ ((qW W (Φ.β y) (fun u ↦ μ (i, u)) : ℤ) : ℝ))
      (fun i _ ↦ hq0 _) (Finset.mem_univ i))
    rw [div_lt_iff₀' hsc] at h2; rw [← Real.lt_log_iff_exp_lt hε]; linarith
  · rw [sum_orbit_eq C hC1 hC2 hC3 (k y) (hk y) T _ (fun μ ↦ hSfin.mem_toFinset) (fun i ν ↦ t y ν (κ i)),
      ← sub_add_sub_cancel _ (ev' y F), max_comm]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max hgF ?_)
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le fun c hc ↦ ?_
    rw [map_prod]
    refine (norm_prod_sub_le _ _ _ _ hε'.le (min_le_right _ _) (fun i ↦ hle y _) fun i ↦ ?_).trans (min_le_left _ _)
    exact hS₀ _ _ _ (fun ν hν ↦ (Finset.mem_filter.1 hν).2) fun ν hν hν' ↦ Finset.mem_filter.2
      ⟨Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hν⟩⟩), hν'⟩

end GlobalTheory.Poinc.OrbTrace
