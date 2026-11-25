module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

open IsLocalRing

namespace GlobalTheory.CompleteDiscreteValuationRing

theorem fg_of_mem {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (a : A) (ha : algebraMap A B a ≠ 0)
    (hart : IsArtinian A (A ⧸ Ideal.span {a}))
    (hden : ∀ x : B, ∃ (n : ℕ) (r : A), algebraMap A B a ^ n * x = algebraMap A B r)
    (J : Ideal B) (hJ : algebraMap A B a ∈ J) : J.FG := by
  set α := algebraMap A B a with hα
  let D : ℕ → Ideal A := fun n => (Ideal.span {α ^ n}).comap (algebraMap A B)
  let E : ℕ →o (Submodule A (A ⧸ Ideal.span {a}))ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (Submodule.map (Ideal.span {a}).mkQ (D n)),
      fun _ _ h => Submodule.map_mono (Ideal.comap_mono
        (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)))⟩
  obtain ⟨l, hl⟩ := IsArtinian.monotone_stabilizes E
  have key : ∀ n, l ≤ n → ∀ r : A, α ^ n ∣ algebraMap A B r →
      ∃ (b : B) (s : A), algebraMap A B r = α ^ (n + 1) * b + α * algebraMap A B s := fun n hn r hr => by
    have h1 : Submodule.map (Ideal.span {a}).mkQ (D n) =
        Submodule.map (Ideal.span {a}).mkQ (D (n + 1)) :=
      (hl n hn).symm.trans (hl (n + 1) (by lia))
    obtain ⟨r', hr', e⟩ : (Ideal.span {a}).mkQ r ∈ Submodule.map (Ideal.span {a}).mkQ (D (n + 1)) :=
      h1 ▸ Submodule.mem_map_of_mem (Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 hr))
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 ((Submodule.Quotient.eq _).1 e.symm)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 hr')
    exact ⟨b, s, by rw [← hb, hα, ← map_mul, ← hs, ← map_add]; congr 1; ring⟩
  have down : ∀ (x : B) (j : ℕ),
      (∃ (b : B) (r : A), α ^ (l + j) * x = α ^ (l + j + 1) * b + algebraMap A B r) →
      ∃ (b : B) (r : A), α ^ l * x = α ^ (l + 1) * b + algebraMap A B r := fun x j => by
    induction j with
    | zero => exact id
    | succ j ih =>
      rintro ⟨b, r, h⟩
      obtain ⟨b', s, hs⟩ := key (l + (j + 1)) (by lia) r ⟨x - α * b, by rw [mul_sub, h]; ring⟩
      refine ih ⟨b + b', s, mul_left_cancel₀ ha ?_⟩
      rw [hs] at h; linear_combination h
  let Q : Ideal B := Ideal.span {α ^ (l + 1)}
  let φ : B →ₗ[B] B ⧸ Q := Q.mkQ ∘ₗ LinearMap.mul B B (α ^ l)
  refine Submodule.fg_of_fg_map_of_fg_inf_ker φ ?_ ?_
  · refine Submodule.FG.of_restrictScalars A
      (Submodule.FG.of_le (Submodule.fg_span_singleton (R := A) (1 : B ⧸ Q)) ?_)
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨n, r₀, h₀⟩ := hden x
    obtain ⟨b, r, h⟩ := down x n ⟨0, a ^ l * r₀, by rw [map_mul, map_pow, ← hα, ← h₀]; ring⟩
    refine Submodule.mem_span_singleton.2 ⟨r, ?_⟩
    change r • (1 : B ⧸ Q) = Ideal.Quotient.mk Q (α ^ l * x)
    rw [h, map_add, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_span_singleton.2 (dvd_mul_right _ _)), zero_add, Algebra.smul_def, mul_one]
    rfl
  · suffices (J : Submodule B B) ⊓ LinearMap.ker φ = Ideal.span {α} by
      rw [this]; exact Submodule.fg_span_singleton _
    refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 ⟨hJ, ?_⟩)
    · rintro x ⟨-, hx⟩
      have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
      rw [pow_succ] at h2
      exact Ideal.mem_span_singleton.2 ((mul_dvd_mul_iff_left (pow_ne_zero l ha)).1 h2)
    · change Ideal.Quotient.mk Q (α ^ l * α) = 0
      rw [← pow_succ]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

theorem exists_dvr_of_dim_one (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O] (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : O →+* W), Function.Injective f ∧ ¬ IsUnit (f t) := by
  let K := FractionRing O
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap O K)
  let f : O →+* B := (algebraMap O K).codRestrict B.toSubring hB
  have finj : Function.Injective f := fun _ _ h =>
    IsFractionRing.injective O K (congrArg Subtype.val h)
  have hft : ¬ IsUnit (f t) := fun h => ht (hloc.1 _ h)
  have hpow : ∀ s : O, s ≠ 0 → ∃ n : ℕ, s ∣ t ^ n := fun s hs => by
    obtain ⟨n, hn⟩ : t ∈ (Ideal.span {s}).radical :=
      (Ideal.radical_eq_sInf (Ideal.span {s})).symm ▸ Submodule.mem_sInf.2 fun P ⟨hP, hP'⟩ =>
        IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 inferInstance P
          (fun h => hs (by simpa [h] using hP)) hP') ▸ ht
    exact ⟨n, Ideal.mem_span_singleton.1 hn⟩
  have hfrac : ∀ x : B, ∃ r s : O, s ≠ 0 ∧ f s * x = f r := fun x => by
    obtain ⟨r, s, hs, e⟩ := IsFractionRing.div_surjective (A := O) (x : K)
    have hs0 := nonZeroDivisors.ne_zero hs
    refine ⟨r, s, hs0, Subtype.ext ?_⟩
    change algebraMap O K s * (x : K) = algebraMap O K r
    rw [← e]
    exact mul_div_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hs0)
  let : Algebra O B := f.toAlgebra
  have hN : IsNoetherianRing B := (isNoetherianRing_iff_ideal_fg B).2 fun J => by
    by_cases hJ : J = ⊥
    · rw [hJ]; exact Submodule.fg_bot
    obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    obtain ⟨r, s, hs, e⟩ := hfrac x
    have hr : r ≠ 0 := fun h => mul_ne_zero ((map_ne_zero_iff f finj).2 hs) hx0 (by simpa [h] using e)
    obtain ⟨n, c, hc⟩ := hpow r hr
    have hne : t ^ (n + 1) ≠ 0 := pow_ne_zero _ ht0
    refine fg_of_mem (t ^ (n + 1)) ((map_ne_zero_iff f finj).2 hne)
      (isFiniteLength_iff_isNoetherian_isArtinian.1
        (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hne))).2 ?_ J ?_
    · intro y
      obtain ⟨r', s', hs', e'⟩ := hfrac y
      obtain ⟨m, c', hc'⟩ := hpow s' hs'
      refine ⟨m, r' * c' * t ^ (n * m), ?_⟩
      change f _ ^ m * y = f _
      rw [map_mul, map_mul, ← e', ← map_pow, ← pow_mul, add_mul, one_mul, pow_add, hc',
        map_mul, map_mul]
      ring
    · change f _ ∈ J
      rw [pow_succ, hc, map_mul, map_mul, ← e]
      exact J.mul_mem_right _ (J.mul_mem_right _ (J.mul_mem_left _ hxJ))
  have : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  exact ⟨B, inferInstance, inferInstance,
    ⟨fun h => ht0 ((map_eq_zero_iff f finj).1 (Ideal.mem_bot.1 (h ▸ (hft : f t ∈ maximalIdeal B))))⟩,
    f, finj, hft⟩

theorem dvr_of_principal (S : Type) [CommRing S] [IsLocalRing S] (p : S)
    (hp : maximalIdeal S = Ideal.span {p}) (hreg : p ∈ nonZeroDivisors S)
    [IsHausdorff (maximalIdeal S) S] :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = p ^ n * u := fun x hx => by
    have hex : ∃ n : ℕ, ¬ p ^ n ∣ x := by
      by_contra h; push Not at h
      refine hx (IsHausdorff.haus (I := maximalIdeal S) inferInstance x fun n => ?_)
      rw [SModEq.zero, hp, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
      exact Ideal.mem_span_singleton.2 (h n)
    have h1 := Nat.find_spec hex
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (n := Nat.find hex) fun h => by simp [h] at h1
    obtain ⟨u, hu⟩ := not_not.1 (Nat.find_min hex (m := n) (by lia))
    refine ⟨n, u, by_contra fun hnu => h1 ?_, hu⟩
    rw [hn, hu, pow_succ]
    exact mul_dvd_mul_left _ (Ideal.mem_span_singleton.1 (hp ▸ (hnu : u ∈ maximalIdeal S)))
  have : NoZeroDivisors S := ⟨fun {x y} h => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · obtain ⟨n, u, hu, rfl⟩ := hfac x hx
      exact Or.inr ((mul_mem (pow_mem hreg n) hu.mem_nonZeroDivisors).1 y h)⟩
  have hdom : IsDomain S := NoZeroDivisors.to_isDomain S
  have hprime : Prime p :=
    (Ideal.span_singleton_prime (nonZeroDivisors.ne_zero hreg)).1 (hp ▸ inferInstance)
  refine ⟨hdom, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, hprime.irreducible, fun {x} hx => ?_⟩⟩
  obtain ⟨n, u, hu, rfl⟩ := hfac x hx
  exact ⟨n, hu.unit, rfl⟩

theorem exists_complete (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : B →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧ IsLocalHom f := by
  let W := AdicCompletion (maximalIdeal B) B
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible B
  have h1 : maximalIdeal W = Ideal.span {algebraMap B W p} :=
    AdicCompletion.maximalIdeal_eq_map.trans <|
      (congrArg (Ideal.map (algebraMap B W)) hp.maximalIdeal_eq).trans <| by
        rw [Ideal.map_span, Set.image_singleton]
  have hr : ∀ x : B, x ≠ 0 → algebraMap B W x ∈ nonZeroDivisors W := fun x hx =>
    mem_nonZeroDivisors_iff_left.2 fun y hy =>
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx)
        (by simpa [Algebra.smul_def] using hy)
  obtain ⟨hd, hD⟩ := dvr_of_principal W _ h1 (hr p hp.ne_zero)
  refine ⟨W, inferInstance, hd, hD, algebraMap B W, inferInstance, fun x y h => ?_, inferInstance⟩
  exact sub_eq_zero.1 <| by_contra fun hne =>
    nonZeroDivisors.ne_zero (hr _ hne) (by rw [map_sub, h, sub_self])

theorem exists_complete_dvr (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (t : A) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : A →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧
        ¬ IsUnit (f t) := by
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes fun h => ht (Ideal.span_singleton_eq_top.1 h)
  have := hP.1.1
  let O := Localization.AtPrime P
  have : Ring.KrullDimLE 1 O := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P O]
    exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  have hinj : Function.Injective (algebraMap A O) :=
    IsLocalization.injective O P.primeCompl_le_nonZeroDivisors
  obtain ⟨B, _, _, _, f, hf, hft⟩ := exists_dvr_of_dim_one O (algebraMap A O t)
    ((map_ne_zero_iff _ hinj).2 ht0) fun h =>
      (IsLocalization.AtPrime.isUnit_to_map_iff O P t).1 h (hP.1.2 (Ideal.mem_span_singleton_self t))
  obtain ⟨W, _, _, hW, g, hc, hg, hl⟩ := exists_complete B
  exact ⟨W, inferInstance, inferInstance, hW, g.comp (f.comp (algebraMap A O)), hc,
    hg.comp (hf.comp hinj), fun h => hft (hl.1 _ h)⟩

theorem exists_chart (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A) (g : R →+* A) (t : A),
      Function.Injective g ∧ t ≠ 0 ∧ ¬ IsUnit t ∧ (∀ r ∈ maximalIdeal R, t ∣ g r) ∧
      ∀ i, Associated (g (a i)) (t ^ k i) := by
  classical
  have := Fintype.ofFinite I
  let K := FractionRing V
  let ι : V →+* K := algebraMap V K
  have hι : Function.Injective ι := IsFractionRing.injective V K
  have hψa : ∀ i, ψ (a i) ≠ 0 := fun i => (h i).ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero)
  let d : Polynomial R := Polynomial.X * Polynomial.C (∏ i, a i)
  have hd : d ≠ 0 := mul_ne_zero Polynomial.X_ne_zero <| Polynomial.C_ne_zero.2 <|
    Finset.prod_ne_zero_iff.2 fun i _ e => hψa i (by rw [e, map_zero])
  have hle : Submonoid.powers d ≤ nonZeroDivisors (Polynomial R) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let C := Localization.Away d
  have : IsDomain C := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (algebraMap (Polynomial R) C) := IsLocalization.injective C hle
  let e : Polynomial R →+* K := Polynomial.eval₂RingHom (ι.comp ψ) (ι ϖ)
  have hed : IsUnit (e d) := Ne.isUnit <| by
    simp only [e, d, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C,
      RingHom.comp_apply, map_prod]
    exact mul_ne_zero ((map_ne_zero_iff ι hι).2 hϖ.ne_zero)
      (Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero_iff ι hι).2 (hψa i))
  let φ : C →+* K := IsLocalization.Away.lift d hed
  let τ : C := algebraMap (Polynomial R) C Polynomial.X
  have hRC : ∀ r : R, algebraMap R C r = algebraMap (Polynomial R) C (Polynomial.C r) := fun r =>
    IsScalarTower.algebraMap_apply R (Polynomial R) C r
  have hφτ : φ τ = ι ϖ := by simp [φ, τ, e]
  have hφr : ∀ r : R, φ (algebraMap R C r) = ι (ψ r) := fun r => by simp [hRC, φ, e]
  have hud : IsUnit (algebraMap (Polynomial R) C d) := IsLocalization.Away.algebraMap_isUnit d
  have huτ : IsUnit τ := isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right _ _)) hud
  have hua : ∀ i, IsUnit (algebraMap R C (a i)) := fun i => by
    rw [hRC]
    exact isUnit_of_dvd_unit (map_dvd _ (Dvd.dvd.mul_left (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))) _)) hud
  have hdiv : ∀ (x y : C) (x' y' : V), IsUnit y → φ x = ι x' → φ y = ι y' → y' ∣ x' →
      ∃ z : C, x = y * z ∧ φ z ∈ ι.range := by
    rintro x y _ y' hy hx' hy' ⟨c, rfl⟩
    obtain ⟨z, rfl⟩ := hy.dvd (a := x)
    exact ⟨z, rfl, c, mul_left_cancel₀ (hy.map φ).ne_zero (by rw [← map_mul, hx', hy', map_mul])⟩
  have hτk : ∀ i, φ (τ ^ k i) = ι (ϖ ^ k i) := fun i => by rw [map_pow, map_pow, hφτ]
  choose u hu hu' using fun i => hdiv (algebraMap R C (a i)) (τ ^ k i) _ _ (huτ.pow _) (hφr _) (hτk i) (h i).symm.dvd
  choose w hw hw' using fun i => hdiv (τ ^ k i) (algebraMap R C (a i)) _ _ (hua i) (hτk i) (hφr _) (h i).dvd
  obtain ⟨s, hs⟩ := (maximalIdeal R).fg_of_isNoetherianRing
  choose z hz hz' using fun y : s => hdiv (algebraMap R C y) τ _ _ huτ (hφr _) hφτ <|
    (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton).1 fun h => (hs ▸ Ideal.subset_span y.2) (hψ.1 _ h)
  let S : Set C := {τ} ∪ Set.range u ∪ Set.range w ∪ Set.range z
  have hS : S.Finite := (((Set.finite_singleton _).union (Set.finite_range _)).union (Set.finite_range _)).union
    (Set.finite_range _)
  let A := Algebra.adjoin R S
  have : Algebra.FiniteType R A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
  have hA : ∀ x ∈ A, φ x ∈ ι.range :=
    Algebra.adjoin_le (S := ({ (ι.range.comap φ).toSubsemiring with
      algebraMap_mem' := fun r => ⟨ψ r, (hφr r).symm⟩ } : Subalgebra R C)) <| by
        rintro _ (((rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
        exacts [⟨_, hφτ.symm⟩, hu' i, hw' i, hz' i]
  refine ⟨A, inferInstance, inferInstance, Algebra.FiniteType.isNoetherianRing R A, algebraMap R A,
    ⟨τ, Algebra.subset_adjoin (Or.inl (Or.inl (Or.inl rfl)))⟩,
    fun x y hxy => by
      have h1 : algebraMap R C x = algebraMap R C y := congrArg Subtype.val hxy
      exact Polynomial.C_injective (hinj (by rwa [hRC, hRC] at h1)),
    fun h0 => huτ.ne_zero (congrArg Subtype.val h0), fun h0 => ?_, fun r hr => ?_, fun i => associated_of_dvd_dvd
      ⟨⟨_, Algebra.subset_adjoin (Or.inl (Or.inr ⟨i, rfl⟩))⟩, Subtype.ext (hw i)⟩
      ⟨⟨_, Algebra.subset_adjoin (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))⟩, Subtype.ext (hu i)⟩⟩
  · obtain ⟨x, hx⟩ := isUnit_iff_exists_inv.1 h0
    obtain ⟨v, hv⟩ := hA x x.2
    have h2 := congrArg φ (show τ * (x : C) = 1 from congrArg Subtype.val hx)
    rw [map_mul, map_one, hφτ, ← hv, ← map_mul, ← map_one ι] at h2
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (hι h2))
  · rw [← Ideal.mem_span_singleton, ← Ideal.mem_comap]
    exact Ideal.span_le.2 (fun y hy => Ideal.mem_comap.2 (Ideal.mem_span_singleton.2
      ⟨⟨_, Algebra.subset_adjoin (Or.inr ⟨⟨y, hy⟩, rfl⟩)⟩, Subtype.ext (hz ⟨y, hy⟩)⟩)) (hs ▸ hr)

theorem main (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W)
      (ψ' : R →+* W) (m : ℕ) (m' : ℕ) (k' : I → ℕ),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧
        IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧
        ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  obtain ⟨A, _, _, _, g, t, hg, ht0, ht, hm, ha⟩ := exists_chart R V ϖ hϖ ψ hψ I a k h
  obtain ⟨W, _, _, hW, f, hc, hf, hft⟩ := exists_complete_dvr A t ht0 ht
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f hf).2 ht0) hp
  refine ⟨W, inferInstance, inferInstance, hW, p, f.comp g, 1, n, fun i => n * k i, hc, hp,
    hf.comp hg, ⟨fun r hr => by_contra fun hnu => hft (isUnit_of_dvd_unit (map_dvd f (hm r hnu)) hr)⟩,
    le_rfl, Nat.one_le_iff_ne_zero.2 fun h0 => hft (by simpa [h0] using hn),
    fun i => ⟨by
      have h1 := (ha i).map f; rw [map_pow] at h1; rw [pow_mul]; exact h1.trans hn.pow_pow, one_mul _⟩⟩

end GlobalTheory.CompleteDiscreteValuationRing
