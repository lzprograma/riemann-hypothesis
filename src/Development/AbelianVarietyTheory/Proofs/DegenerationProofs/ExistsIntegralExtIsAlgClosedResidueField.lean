module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

namespace GlobalTheory.ClosedResidueExt

open Polynomial IsLocalRing

variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]

def Unram (π : W) (R : Subalgebra W Ω) : Prop :=
  (∀ x ∈ R, IsIntegral W x) ∧ (algebraMap W Ω π)⁻¹ ∉ R ∧
    ∀ x ∈ R, x ≠ 0 → ∃ (n : ℕ) (u : Ω), u ∈ R ∧ u⁻¹ ∈ R ∧ x = algebraMap W Ω π ^ n * u

private lemma exists_maximal_unram_subalgebra (π : W) (h0 : Unram π (⊥ : Subalgebra W Ω)) :
    ∃ M : Subalgebra W Ω, Unram π M ∧ ∀ N, Unram π N → M ≤ N → N = M := by
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ {R : Subalgebra W Ω | Unram π R}
    (fun c hc hchain y hy => by
      have : Nonempty c := ⟨⟨y, hy⟩⟩
      have hmem : ∀ x ∈ ⨆ R : c, (R : Subalgebra W Ω), ∃ R : c, x ∈ (R : Subalgebra W Ω) := fun x hx =>
        Set.mem_iUnion.1 (Subalgebra.coe_iSup_of_directed hchain.directed ▸ hx)
      refine ⟨⨆ R : c, (R : Subalgebra W Ω), ⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩,
        fun R hR => le_iSup (fun R : c => (R : Subalgebra W Ω)) ⟨R, hR⟩⟩
      · obtain ⟨R, hR⟩ := hmem x hx; exact (hc R.2).1 x hR
      · obtain ⟨R, hR⟩ := hmem _ hx; exact (hc R.2).2.1 hR
      · obtain ⟨R, hR⟩ := hmem x hx
        obtain ⟨n, u, hu, hu', e⟩ := (hc R.2).2.2 x hR hx0
        exact ⟨n, u, le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu,
          le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu', e⟩) ⊥ h0
  exact ⟨M, hM.prop, fun N hN hle => (hM.eq_of_le hN hle).symm⟩

private lemma irreducible_and_associated_pow_of_unram {π : W} (M : Subalgebra W Ω) (hM : Unram π M) :
    Irreducible (algebraMap W M π) ∧ ∀ x : M, x ≠ 0 → ∃ n : ℕ, Associated (algebraMap W M π ^ n) x := by
  obtain ⟨-, hinv, hfac⟩ := hM
  have hp0 : algebraMap W Ω π ≠ 0 := fun h => hinv (by simp [h])
  have unit_of : ∀ (a : M) (u : Ω), u⁻¹ ∈ M → (a : Ω) = u → u ≠ 0 → IsUnit a := fun a u hu' e hu0 =>
    IsUnit.of_mul_eq_one ⟨u⁻¹, hu'⟩ (Subtype.ext (by simp [e, mul_inv_cancel₀ hu0]))
  refine ⟨⟨fun hu => ?_, fun a b hab => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hmul : (y : Ω) * algebraMap W Ω π = 1 := by
      simpa [mul_comm] using congrArg Subtype.val hy
    exact hinv (eq_inv_of_mul_eq_one_left hmul ▸ y.2)
  · have hab' : algebraMap W Ω π = (a : Ω) * b := congrArg Subtype.val hab
    have ha0 : (a : Ω) ≠ 0 := fun h => hp0 (by rw [hab', h, zero_mul])
    have hb0 : (b : Ω) ≠ 0 := fun h => hp0 (by rw [hab', h, mul_zero])
    obtain ⟨i, u, hu, hu', ea⟩ := hfac a a.2 ha0
    obtain ⟨j, v, hv, hv', eb⟩ := hfac b b.2 hb0
    have hu0 : u ≠ 0 := fun h => ha0 (by rw [ea, h, mul_zero])
    have hv0 : v ≠ 0 := fun h => hb0 (by rw [eb, h, mul_zero])
    rcases i with _ | i
    · exact Or.inl (unit_of a u hu' (by simpa using ea) hu0)
    rcases j with _ | j
    · exact Or.inr (unit_of b v hv' (by simpa using eb) hv0)
    have key : (algebraMap W Ω π)⁻¹ = algebraMap W Ω π ^ (i + j) * u * v :=
      inv_eq_of_mul_eq_one_right <| mul_left_cancel₀ hp0 <| by
        rw [mul_one]
        calc algebraMap W Ω π * (algebraMap W Ω π * (algebraMap W Ω π ^ (i + j) * u * v))
            = algebraMap W Ω π ^ (i + 1) * u * (algebraMap W Ω π ^ (j + 1) * v) := by ring
          _ = algebraMap W Ω π := by rw [← ea, ← eb, hab']
    exact False.elim <| hinv <| key ▸ M.mul_mem (M.mul_mem (M.pow_mem (M.algebraMap_mem π) _) hu) hv
  · have hx0 : (x : Ω) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨n, u, hu, hu', e⟩ := hfac x x.2 hx0
    obtain ⟨U, hU⟩ := unit_of ⟨u, hu⟩ u hu' rfl fun h => hx0 (by rw [e, h, mul_zero])
    exact ⟨n, U, Subtype.ext (by simp [hU, e])⟩

private lemma isUnit_one_add_algebraMap_mul_of_not_isUnit [IsLocalRing W] {π : W} (hπ : ¬ IsUnit π)
    (N : Subalgebra W Ω) (hN : ∀ x ∈ N, IsIntegral W x) (h : N) : IsUnit (1 + algebraMap W N π * h) := by
  by_contra hu
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap W N π * h})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have : Algebra.IsIntegral W N :=
    ⟨fun x => (isIntegral_algHom_iff N.val Subtype.val_injective).1 (hN x x.2)⟩
  have hc : m.comap (algebraMap W N) = maximalIdeal W :=
    eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal m)
  have hπm : algebraMap W N π ∈ m := Ideal.mem_comap.1 (hc ▸ hπ)
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2
    (by simpa using m.sub_mem (hle (Ideal.subset_span rfl)) (m.mul_mem_right h hπm)))

private lemma eq_pow_mul_unit_of_mem_adjoin [IsLocalRing W] {π : W}
    (hπ : ¬ IsUnit π) (M : Subalgebra W Ω) [WfDvdMonoid M] {k : Type} [Field k] (φ : M →+* k)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {algebraMap W M π}) (f : M[X])
    (hf : f.Monic) (hirr : Irreducible (f.map φ)) (α : Ω) (hα : aeval α f = 0)
    (hN : ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, IsIntegral W x) :
    ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, x ≠ 0 → ∃ (n : ℕ) (u : Ω),
      u ∈ (Algebra.adjoin M {α}).restrictScalars W ∧ u⁻¹ ∈ (Algebra.adjoin M {α}).restrictScalars W ∧
      x = algebraMap W Ω π ^ n * u := by
  set N := (Algebra.adjoin M {α}).restrictScalars W
  have memN : ∀ g : M[X], aeval α g ∈ N := fun g => by
    show aeval α g ∈ Algebra.adjoin M {α}
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨g, rfl⟩
  intro x hx hx0
  have hx' : x ∈ Algebra.adjoin M {α} := hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨g0, rfl⟩ := hx'
  change aeval α g0 ≠ 0 at hx0
  show ∃ (n : ℕ) (u : Ω), u ∈ N ∧ u⁻¹ ∈ N ∧ aeval α g0 = algebraMap W Ω π ^ n * u
  set g := g0 %ₘ f
  have hg : aeval α g = aeval α g0 := by
    conv_rhs => rw [← modByMonic_add_div g0 f]
    simp [g, hα]
  have hgdeg : g.natDegree < f.natDegree :=
    natDegree_modByMonic_lt g0 hf fun h => hirr.not_isUnit (by simp [h])
  have hg0 : g ≠ 0 := fun h => hx0 (by rw [← hg, h, map_zero])
  have hπC : ¬ IsUnit (C (algebraMap W M π)) := fun hu =>
    RingHom.ker_ne_top φ (Ideal.eq_top_of_isUnit_mem _ (hker ▸ Ideal.subset_span rfl) (isUnit_C.1 hu))
  obtain ⟨n, g1, hndvd, hgeq⟩ := WfDvdMonoid.max_power_factor' hg0 hπC
  have hker_map : RingHom.ker (mapRingHom φ) = Ideal.span {C (algebraMap W M π)} := by
    rw [ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton]
  have hmap1 : g1.map φ ≠ 0 := fun h0 =>
    hndvd (Ideal.mem_span_singleton.1 (hker_map ▸ (h0 : g1 ∈ RingHom.ker (mapRingHom φ))))
  have hdeg1 : g1.natDegree ≤ g.natDegree := by
    rw [hgeq, natDegree_mul (fun h => hg0 (by rw [hgeq, h, zero_mul]))
      (fun h => hg0 (by rw [hgeq, h, mul_zero]))]
    omega
  have hndvdp : ¬ f.map φ ∣ g1.map φ := fun hd => by
    have h1 := hf.natDegree_map φ ▸ natDegree_le_of_dvd hd hmap1
    have h2 := natDegree_map_le (f := φ) (p := g1)
    omega
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.2 hndvdp
  obtain ⟨A, rfl⟩ := Polynomial.map_surjective φ hφ a
  obtain ⟨B, rfl⟩ := Polynomial.map_surjective φ hφ b
  have hker2 : A * f + B * g1 - 1 ∈ Ideal.span {C (algebraMap W M π)} :=
    hker_map ▸ show (A * f + B * g1 - 1).map φ = 0 by simp [hab]
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.1 hker2
  have hev : aeval α B * aeval α g1 = 1 + algebraMap W Ω π * aeval α H := by
    have h := congrArg (aeval α) hH
    simp only [map_sub, map_add, map_mul, map_one, hα, mul_zero, zero_add, aeval_C] at h
    rw [IsScalarTower.algebraMap_apply W M Ω]; linear_combination h
  obtain ⟨w, hw⟩ :=
    (isUnit_one_add_algebraMap_mul_of_not_isUnit hπ N hN ⟨aeval α H, memN H⟩).exists_left_inv
  have hv : (w : Ω) * (1 + algebraMap W Ω π * aeval α H) = 1 := congrArg Subtype.val hw
  refine ⟨n, aeval α g1, memN g1, ?_, by rw [← hg, hgeq, map_mul, map_pow, aeval_C, IsScalarTower.algebraMap_apply W M Ω]⟩
  have hinv : (aeval α g1)⁻¹ = (w : Ω) * aeval α B :=
    inv_eq_of_mul_eq_one_right (by linear_combination (w : Ω) * hev + hv)
  exact hinv ▸ N.mul_mem w.2 (memN B)

theorem _root_.GlobalTheory.ClosedResidueExt.exists_unramified_ext (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        Irreducible (algebraMap W R π) ∧ IsAlgClosed (ResidueField R) := by
  let Ω := AlgebraicClosure (FractionRing W)
  have hinj : Function.Injective (algebraMap W Ω) :=
    IsScalarTower.algebraMap_eq W (FractionRing W) Ω ▸
      (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  have h0 : Unram π (⊥ : Subalgebra W Ω) := by
    refine ⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩
    · obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hx; exact isIntegral_algebraMap
    · obtain ⟨w, hw⟩ := Algebra.mem_bot.1 hx
      have hp0 : algebraMap W Ω π ≠ 0 := fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))
      exact hπ.not_isUnit (IsUnit.of_mul_eq_one w (hinj (by rw [map_mul, hw, map_one, mul_inv_cancel₀ hp0])))
    · obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hx
      have hw0 : w ≠ 0 := fun h => hx0 (by rw [h, map_zero])
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hπ
      have hinv : (algebraMap W Ω (u : W))⁻¹ = algebraMap W Ω ((u⁻¹ : Wˣ) : W) :=
        inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
      exact ⟨n, algebraMap W Ω u, Subalgebra.algebraMap_mem _ _,
        hinv ▸ Subalgebra.algebraMap_mem _ _, by rw [hu, map_mul, map_pow, mul_comm]⟩
  obtain ⟨M, hM, hmax⟩ := exists_maximal_unram_subalgebra π h0
  obtain ⟨hirrM, hfacM⟩ := irreducible_and_associated_pow_of_unram M hM
  have : IsDiscreteValuationRing M :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirrM, fun {x} hx => hfacM x hx⟩
  have hint : Algebra.IsIntegral W M :=
    ⟨fun x => (isIntegral_algHom_iff M.val Subtype.val_injective).1 (hM.1 x x.2)⟩
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ _ hab => hinj (congrArg Subtype.val hab), hint, hirrM,
    IsAlgClosed.of_exists_root _ fun p hpm hpirr => ?_⟩
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue M) residue_surjective p
  obtain ⟨f, hfp, hfnat, hfm⟩ := lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 ⟨q, hq⟩) hpm
  have hfdeg : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hfm.ne_zero, hfnat]
    exact_mod_cast (natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hpirr)).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero Ω f hfdeg
  have hNint : ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, IsIntegral W x := fun x hx =>
    isIntegral_trans x (adjoin_le_integralClosure ⟨f, hfm, hα⟩ hx)
  have hker : RingHom.ker (residue M) = Ideal.span {algebraMap W M π} :=
    ker_residue.trans ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirrM)
  have hp0 : algebraMap W Ω π ≠ 0 := fun h => hM.2.1 (by simp [h])
  have hNU : Unram π ((Algebra.adjoin M {α}).restrictScalars W) := by
    refine ⟨hNint, fun hx => ?_, eq_pow_mul_unit_of_mem_adjoin hπ.not_isUnit M (residue M)
      residue_surjective hker f hfm (hfp ▸ hpirr) α hα hNint⟩
    have hu := isUnit_one_add_algebraMap_mul_of_not_isUnit hπ.not_isUnit _ hNint
      ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩
    have hz : (1 + algebraMap W ((Algebra.adjoin M {α}).restrictScalars W) π *
        ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩ : (Algebra.adjoin M {α}).restrictScalars W) = 0 :=
      Subtype.ext (by
        show (1 : Ω) + algebraMap W Ω π * -(algebraMap W Ω π)⁻¹ = 0
        rw [mul_neg, mul_inv_cancel₀ hp0, add_neg_cancel])
    exact not_isUnit_zero (hz ▸ hu)
  have hNM := hmax _ hNU fun x hx => Subalgebra.algebraMap_mem (Algebra.adjoin M {α}) (⟨x, hx⟩ : M)
  have hαM : α ∈ M := hNM ▸ (Algebra.self_mem_adjoin_singleton M α : α ∈ Algebra.adjoin M {α})
  have hev : eval (⟨α, hαM⟩ : M) f = 0 := Subtype.ext <| by
    have h := hα
    rw [show α = algebraMap M Ω ⟨α, hαM⟩ from rfl, aeval_algebraMap_apply_eq_algebraMap_eval] at h
    exact h
  exact ⟨residue M ⟨α, hαM⟩, by rw [← hfp, eval_map, eval₂_hom, hev, map_zero]⟩

theorem _root_.GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W],
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        IsAlgClosed (IsLocalRing.ResidueField R) := by
  intro W _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨R, i1, i2, i3, i4, h1, h2, _, h4⟩ := exists_unramified_ext W hπ
  exact ⟨R, i1, i2, i3, i4, h1, h2, h4⟩

end GlobalTheory.ClosedResidueExt
