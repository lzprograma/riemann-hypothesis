module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Arith
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

@[expose] public section

open NumberField Matrix

namespace PositivityTheory.KB.SpectralGap

section

variable {L : Type} [Field L] [NumberField L] {N : ℕ} {π : 𝓞 L}

private theorem mem_Kg_iff (hπ : (π : L) ≠ 0) {r : ℕ} {g : SpecialLinearGroup (Fin N) L} :
    g ∈ Kg L N π r ↔ ∀ i j : Fin N, ∃ z : 𝓞 L,
      (if (i : ℕ) < r then (π : L) else 1) * g i j = z * if (j : ℕ) < r then (π : L) else 1 := by
  refine ⟨fun ⟨γ, hγ⟩ i j =>
    ⟨γ i j, by simpa [dg, mt, mo, diagonal_mul, mul_diagonal] using congrFun (congrFun hγ i) j⟩, fun h => ?_⟩
  choose z hz using h
  have hD : (dg L N π r).det ≠ 0 := by rw [dg, det_diagonal, Finset.prod_ne_zero_iff]; intro i _; split_ifs <;> simp [hπ]
  have hmat : dg L N π r * (g : Matrix (Fin N) (Fin N) L) = (of z).map (algebraMap (𝓞 L) L) * dg L N π r := by
    ext i j; simpa [dg, diagonal_mul, mul_diagonal] using hz i j
  have hdet : (of z).det = 1 := FaithfulSMul.algebraMap_injective (𝓞 L) L <| by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_one]
    exact mul_right_cancel₀ hD (by simpa [det_mul, g.prop] using (congrArg det hmat).symm)
  refine ⟨⟨of z, hdet⟩, ?_⟩; convert hmat using 2 <;> [rfl; (ext i j; rfl)]

private theorem twoTr_Kg_of_iff (hπ : (π : L) ≠ 0) (r : ℕ) (E : Subgroup (SpecialLinearGroup (Fin N) L))
    (S : SpecialLinearGroup (Fin N) (𝓞 L) → Prop)
    (hS : ∀ {γ δ}, ¬S γ → ¬S δ → ∃ ξ, S ξ ∧ ∃ η, S η ∧ δ = ξ * γ * η)
    (hES : ∀ {g γ}, dg L N π r * mt L N g = mo L N γ * dg L N π r → (g ∈ E ↔ S γ)) : TwoTr E (Kg L N π r) := by
  have hU : IsUnit (dg L N π r).det := IsUnit.mk0 _ (by rw [dg, det_diagonal, Finset.prod_ne_zero_iff]; intro i _; split_ifs <;> simp [hπ])
  have hconj (ξ : SpecialLinearGroup (Fin N) (𝓞 L)) : ∃ e, dg L N π r * mt L N e = mo L N ξ * dg L N π r := by
    have hmo : (mo L N ξ).det = 1 := by
      show ((ξ : Matrix (Fin N) (Fin N) (𝓞 L)).map (algebraMap (𝓞 L) L)).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ξ.prop, map_one]
    refine ⟨⟨(dg L N π r)⁻¹ * mo L N ξ * dg L N π r,
      by rw [det_mul, det_mul, det_nonsing_inv, hmo, mul_one, Ring.inverse_mul_cancel _ hU]⟩, ?_⟩
    show dg L N π r * ((dg L N π r)⁻¹ * mo L N ξ * dg L N π r) = _
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hU]
  have hmul {a b α β} (ha : dg L N π r * mt L N a = mo L N α * dg L N π r)
      (hb : dg L N π r * mt L N b = mo L N β * dg L N π r) :
      dg L N π r * mt L N (a * b) = mo L N (α * β) * dg L N π r := by
    rw [map_mul, map_mul, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]
  rintro g ⟨γ, hγ⟩ hgE g' ⟨γ', hγ'⟩ hg'E
  obtain ⟨ξ, hξ, η, hη, rfl⟩ := hS (hgE ∘ (hES hγ).mpr) (hg'E ∘ (hES hγ').mpr)
  obtain ⟨e, he⟩ := hconj ξ; obtain ⟨e', he'⟩ := hconj η
  refine ⟨e, (hES he).mpr hξ, e', (hES he').mpr hη, ?_⟩
  have hinj : mt L N g' = mt L N (e * g * e') := by
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul] using
      congrArg ((dg L N π r)⁻¹ * ·) (hγ'.trans (hmul (hmul he hγ) he').symm)
  exact SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun hinj i) j

omit [NumberField L] in
private theorem exists_int_scale_iff (P Q : Prop) [Decidable P] [Decidable Q] (x : 𝓞 L) :
    (∃ z : 𝓞 L, (if P then (π : L) else 1) * x = z * if Q then (π : L) else 1) ↔ (Q → ¬P → π ∣ x) := by
  split_ifs with hP hQ hQ
  · exact ⟨fun _ _ hnP => (hnP hP).elim, fun _ => ⟨x, mul_comm _ _⟩⟩
  · exact ⟨fun _ h _ => (hQ h).elim, fun _ => ⟨π * x, by push_cast; ring⟩⟩
  · refine ⟨fun ⟨z, hz⟩ _ _ => ⟨z, FaithfulSMul.algebraMap_injective (𝓞 L) L (by simpa [mul_comm] using hz)⟩,
      fun H => let ⟨z, hz⟩ := H hQ hP; ⟨z, by simp [hz, mul_comm]⟩⟩
  · exact ⟨fun _ h _ => (hQ h).elim, fun _ => ⟨x, by simp⟩⟩

private theorem mem_Kg_inf_succ_iff (hπ : (π : L) ≠ 0) {r : ℕ} {k : Fin N} (hk : (k : ℕ) = r)
    {g : SpecialLinearGroup (Fin N) L} {γ : SpecialLinearGroup (Fin N) (𝓞 L)}
    (h : dg L N π r * mt L N g = mo L N γ * dg L N π r) :
    g ∈ Kg L N π r ⊓ Kg L N π (r + 1) ↔ ∀ i ≠ k, π ∣ γ i k := by
  rw [Subgroup.mem_inf, and_iff_right ⟨γ, h⟩, mem_Kg_iff hπ]
  have hsucc (a : Fin N) : (if (a : ℕ) < r + 1 then (π : L) else 1) =
      (if a = k then (π : L) else 1) * if (a : ℕ) < r then (π : L) else 1 := by split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hiff (i j : Fin N) : (∃ z : 𝓞 L, (if (i : ℕ) < r + 1 then (π : L) else 1) * g i j =
      z * if (j : ℕ) < r + 1 then (π : L) else 1) ↔ (j = k → i ≠ k → π ∣ γ i j) := by
    have hent : (if (i : ℕ) < r then (π : L) else 1) * g i j = γ i j * if (j : ℕ) < r then (π : L) else 1 := by
      simpa [dg, mt, mo, diagonal_mul, mul_diagonal] using congrFun (congrFun h i) j
    have hdj : (if (j : ℕ) < r then (π : L) else 1) ≠ 0 := by split_ifs <;> simp [hπ]
    rw [hsucc i, hsucc j, ← exists_int_scale_iff (π := π) (i = k) (j = k) (γ i j)]
    exact exists_congr fun z =>
      ⟨fun hz => mul_right_cancel₀ hdj (by linear_combination hz - (if i = k then (π : L) else 1) * hent),
       fun hz => by linear_combination (if i = k then (π : L) else 1) * hent + (if (j : ℕ) < r then (π : L) else 1) * hz⟩
  exact ⟨fun H i hi => (hiff i k).mp (H i k) rfl hi, fun H i j => (hiff i j).mpr fun hj hi => hj ▸ H i hi⟩

private theorem mem_Kg_inf_succ_iff' (hπ : (π : L) ≠ 0) {r : ℕ} {k : Fin N} (hk : (k : ℕ) = r)
    {g : SpecialLinearGroup (Fin N) L} {γ : SpecialLinearGroup (Fin N) (𝓞 L)}
    (h : dg L N π (r + 1) * mt L N g = mo L N γ * dg L N π (r + 1)) :
    g ∈ Kg L N π r ⊓ Kg L N π (r + 1) ↔ ∀ j ≠ k, π ∣ γ k j := by
  rw [Subgroup.mem_inf, and_iff_left ⟨γ, h⟩, mem_Kg_iff hπ]
  have hsucc (a : Fin N) : (if (a : ℕ) < r + 1 then (π : L) else 1) =
      (if a = k then (π : L) else 1) * if (a : ℕ) < r then (π : L) else 1 := by split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hiff (i j : Fin N) : (∃ z : 𝓞 L, (if (i : ℕ) < r then (π : L) else 1) * g i j =
      z * if (j : ℕ) < r then (π : L) else 1) ↔ (i = k → j ≠ k → π ∣ γ i j) := by
    have hent : (if (i : ℕ) < r + 1 then (π : L) else 1) * g i j = γ i j * if (j : ℕ) < r + 1 then (π : L) else 1 := by
      simpa [dg, mt, mo, diagonal_mul, mul_diagonal] using congrFun (congrFun h i) j
    have hci : (if i = k then (π : L) else 1) ≠ 0 := by split_ifs <;> simp [hπ]
    have hdj : (if (j : ℕ) < r then (π : L) else 1) ≠ 0 := by split_ifs <;> simp [hπ]
    rw [hsucc i, hsucc j] at hent; rw [← exists_int_scale_iff (π := π) (j = k) (i = k) (γ i j)]
    exact exists_congr fun z =>
      ⟨fun hz => mul_right_cancel₀ hdj (by linear_combination (if i = k then (π : L) else 1) * hz - hent),
       fun hz => mul_left_cancel₀ hci (by linear_combination hent + (if (j : ℕ) < r then (π : L) else 1) * hz)⟩
  exact ⟨fun H j hj => (hiff k j).mp (H k j) rfl hj, fun H i j => (hiff i j).mpr fun hi hj => hi ▸ H j hj⟩

private theorem absNorm_le_index_Kg (hπ : (π : L) ≠ 0) (s t : ℕ) {a b : Fin N} (hab : a ≠ b)
    (hs : (b : ℕ) < s → (a : ℕ) < s) (hb : (b : ℕ) < t) (ha : ¬(a : ℕ) < t)
    (hBs : Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2 ≤ Kg L N π s) (hBt : Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2 ≤ Kg L N π t)
    (hfin : ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0)).index ≠ 0) :
    Ideal.absNorm (Ideal.span {π}) ≤ ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0 ⊓ Kg L N π s)).index := by
  let tv (x : 𝓞 L) : SpecialLinearGroup (Fin N) L := ⟨transvection a b (x : L), det_transvection_of_ne a b hab _⟩
  have htv (r : ℕ) (x : 𝓞 L) : tv x ∈ Kg L N π r ↔ ((b : ℕ) < r → ¬(a : ℕ) < r → π ∣ x) := by
    rw [mem_Kg_iff hπ, ← exists_int_scale_iff (π := π) ((a : ℕ) < r) ((b : ℕ) < r) x]
    refine ⟨fun H => by simpa [tv, transvection, single_apply, hab] using H a b, fun H i j => ?_⟩
    by_cases hij : i = a ∧ j = b
    · rcases hij with ⟨rfl, rfl⟩; simpa [tv, transvection, single_apply, hab] using H
    · by_cases hdiag : i = j
      · subst hdiag; exact ⟨1, by simp [tv, transvection, show ¬(a = i ∧ b = i) from fun h => hab (h.1.trans h.2.symm)]⟩
      · exact ⟨0, by simp [tv, transvection, Matrix.single, hdiag, show ¬(a = i ∧ b = j) by tauto]⟩
  set B := Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2; set A := Kg L N π 0 ⊓ Kg L N π s
  have : (B.subgroupOf A).FiniteIndex := ⟨left_ne_zero_of_mul
    (by rwa [← Subgroup.relIndex, Subgroup.relIndex_mul_relIndex B A _ (fun _ h => ⟨h.1.1, hBs h⟩) inf_le_left])⟩
  have hfA (x : 𝓞 L) : tv x ∈ A := ⟨(htv 0 x).mpr (by simp), (htv s x).mpr fun hbs has => (has (hs hbs)).elim⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Subgroup.index]
  choose rep hrep using Ideal.Quotient.mk_surjective (I := Ideal.span {π})
  refine Nat.card_le_card_of_injective (fun q => QuotientGroup.mk (⟨tv (rep q), hfA _⟩ : A)) fun q₁ q₂ hq => ?_
  have hmem : (tv (rep q₁))⁻¹ * tv (rep q₂) ∈ B := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hq)
  have hmul : (tv (rep q₁))⁻¹ * tv (rep q₂) = tv (rep q₂ - rep q₁) := by
    rw [inv_mul_eq_iff_eq_mul]; apply Subtype.ext
    show transvection a b (rep q₂ : L) = transvection a b (rep q₁ : L) * transvection a b ((rep q₂ - rep q₁ : 𝓞 L) : L)
    rw [transvection_mul_transvection_same (h := hab)]; congr 1; push_cast; ring
  rw [hmul] at hmem; rw [← hrep q₁, ← hrep q₂]
  exact (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ((htv t _).mp (hBt hmem) hb ha))).symm

private theorem col_twoTr (π : 𝓞 L) (hπ : Prime π) {k m : Fin N} (hkm : k ≠ m)
    {γ δ : SpecialLinearGroup (Fin N) (𝓞 L)} (hγ : ¬∀ i ≠ k, π ∣ γ i k) (hδ : ¬∀ i ≠ k, π ∣ δ i k) :
    ∃ ξ, (∀ i ≠ k, π ∣ ξ i k) ∧ ∃ η, (∀ i ≠ k, π ∣ η i k) ∧ δ = ξ * γ * η := by
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have : (Ideal.span {π}).IsMaximal := hP.isMaximal (Ideal.span_singleton_eq_bot.not.mpr hπ.ne_zero)
  let : Field (𝓞 L ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  set q := Ideal.Quotient.mk (Ideal.span {π})
  have hdvd (x : 𝓞 L) : π ∣ x ↔ q x = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have inv_mul_dvd {X Y : SpecialLinearGroup (Fin N) (𝓞 L)} (r : Fin N) {u u' : 𝓞 L ⧸ Ideal.span {π}} (hu : u ≠ 0)
      (hX : ∀ j, q ((X : Matrix (Fin N) (Fin N) (𝓞 L)) j k) = if j = r then u else 0)
      (hY : ∀ j, q ((Y : Matrix (Fin N) (Fin N) (𝓞 L)) j k) = if j = r then u' else 0) :
      ∀ i ≠ k, π ∣ ((X⁻¹ * Y : SpecialLinearGroup (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) i k := by
    intro i hi; rw [hdvd]
    let M := q.mapMatrix (X : Matrix (Fin N) (Fin N) (𝓞 L))
    let Z := q.mapMatrix ((X⁻¹ * Y : SpecialLinearGroup (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L))
    have hM : IsUnit M := by rw [isUnit_iff_isUnit_det, ← RingHom.map_det, X.prop, map_one]; exact isUnit_one
    have hmv : M *ᵥ (fun j => Z j k) = M *ᵥ Pi.single k (u⁻¹ * u') := by
      ext j; rw [mulVec_single]
      have hXY : (M *ᵥ fun l => Z l k) j = q ((Y : Matrix (Fin N) (Fin N) (𝓞 L)) j k) := by
        change (M * Z) j k = _; simp only [M, Z, ← map_mul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel_left]; rfl
      rw [hXY, hY]; simp only [M, Pi.smul_apply, RingHom.mapMatrix_apply]
      change _ = q ((X : Matrix (Fin N) (Fin N) (𝓞 L)) j k) * (u⁻¹ * u')
      rw [hX]; split_ifs <;> simp [mul_inv_cancel_left₀ hu]
    exact (congrFun (Matrix.mulVec_injective_of_isUnit hM hmv) i).trans (Pi.single_eq_of_ne hi _)
  have step (x : SpecialLinearGroup (Fin N) (𝓞 L)) (hx : ¬∀ i ≠ k, π ∣ x i k) :
      ∃ A : SpecialLinearGroup (Fin N) (𝓞 L), (∀ i, q ((A : Matrix (Fin N) (Fin N) (𝓞 L)) i k) = if i = k then 1 else 0) ∧
        ∃ u : 𝓞 L ⧸ Ideal.span {π}, u ≠ 0 ∧
          ∀ i, q ((A * x : SpecialLinearGroup (Fin N) (𝓞 L)) i k) = if i = m then u else 0 := by
    simp_rw [hdvd] at hx; push Not at hx; obtain ⟨p, hpk, hp⟩ := hx
    have ⟨ε₁, hε₁k, hε₁m⟩ : ∃ ε₁ : SpecialLinearGroup (Fin N) (𝓞 L),
        (∀ i, (ε₁ : Matrix (Fin N) (Fin N) (𝓞 L)) i k = if i = k then 1 else 0) ∧
          q ((ε₁ * x : SpecialLinearGroup (Fin N) (𝓞 L)) m k) ≠ 0 := by
      by_cases hm : q (x m k) = 0
      · refine ⟨⟨transvection m p 1, det_transvection_of_ne m p (fun e => hp (e ▸ hm)) 1⟩, fun i => ?_, ?_⟩
        · show (transvection m p (1 : 𝓞 L)) i k = if i = k then 1 else 0; simp [transvection, Matrix.one_apply, hpk]
        · show q ((transvection m p (1 : 𝓞 L) * x) m k) ≠ 0; simpa [transvection_mul_apply_same, hm] using hp
      · exact ⟨1, fun i => by simp [Matrix.one_apply], by simpa using hm⟩
    set w := ε₁ * x
    obtain ⟨t, ht⟩ : ∃ t, q t = (q ((w : Matrix (Fin N) (Fin N) (𝓞 L)) m k))⁻¹ := Ideal.Quotient.mk_surjective _
    let c : Fin N → 𝓞 L := fun i => if i = m then 0 else -(w i k * t)
    let E : Matrix (Fin N) (Fin N) (𝓞 L) := 1 + replicateCol Unit c * replicateRow Unit (Pi.single m (1 : 𝓞 L))
    let ε₂ : SpecialLinearGroup (Fin N) (𝓞 L) := ⟨E, by rw [det_one_add_replicateCol_mul_replicateRow]; simp [c]⟩
    refine ⟨ε₂ * ε₁, fun i => ?_, q (w m k), hε₁m, fun i => ?_⟩
    · have hEk (j : Fin N) : E j k = if j = k then 1 else 0 := by simp [E, Matrix.one_apply, Matrix.mul_apply, hkm]
      rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      simp [show (ε₂ : Matrix (Fin N) (Fin N) (𝓞 L)) = E from rfl, hε₁k, hEk, apply_ite q]
    · have hEw : (E * (w : Matrix (Fin N) (Fin N) (𝓞 L))) i k = w i k + c i * w m k := by
        simp [E, Matrix.mul_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, Pi.single_apply]
      rw [mul_assoc, SpecialLinearGroup.coe_mul, show (ε₂ : Matrix (Fin N) (Fin N) (𝓞 L)) = E from rfl, hEw]
      by_cases him : i = m; · simp [c, him]
      simp only [c, him, ite_false, neg_mul, map_add, map_neg, map_mul, mul_assoc, ht,
        inv_mul_cancel₀ hε₁m, mul_one, add_neg_cancel]
  obtain ⟨A, hAk, u, hu, hAu⟩ := step γ hγ; obtain ⟨B, hBk, u', _, hBu⟩ := step δ hδ
  exact ⟨B⁻¹ * A, inv_mul_dvd k one_ne_zero hBk hAk, (A * γ)⁻¹ * (B * δ), inv_mul_dvd m hu hAu hBu, by group⟩

private theorem row_twoTr (π : 𝓞 L) (hπ : Prime π) {k m : Fin N} (hkm : k ≠ m)
    {γ δ : SpecialLinearGroup (Fin N) (𝓞 L)} (hγ : ¬∀ j ≠ k, π ∣ γ k j) (hδ : ¬∀ j ≠ k, π ∣ δ k j) :
    ∃ ξ, (∀ j ≠ k, π ∣ ξ k j) ∧ ∃ η, (∀ j ≠ k, π ∣ η k j) ∧ δ = ξ * γ * η := by
  let T (x : SpecialLinearGroup (Fin N) (𝓞 L)) : SpecialLinearGroup (Fin N) (𝓞 L) :=
    ⟨(x : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, by rw [det_transpose]; exact x.prop⟩
  have hT (x) : (T x : Matrix (Fin N) (Fin N) (𝓞 L)) = (x : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ := rfl
  obtain ⟨ξ, hξ, η, hη, h⟩ := col_twoTr π hπ hkm (γ := T γ) (δ := T δ) hγ hδ
  refine ⟨T η, hη, T ξ, hξ, SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  have h2 := congrArg (fun x : SpecialLinearGroup (Fin N) (𝓞 L) => (x : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ i j) h
  simp only [SpecialLinearGroup.coe_mul, hT, Matrix.transpose_mul, Matrix.transpose_transpose] at h2
  rw [h2, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hT, hT, Matrix.mul_assoc]

private theorem index_Kg_triple_ne_zero (π : 𝓞 L) (hπ : Prime π) (N r : ℕ) :
    ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π r)).index ≠ 0 := by
  have hπ0 : (π : L) ≠ 0 := by simpa using (FaithfulSMul.algebraMap_injective (𝓞 L) L).ne hπ.ne_zero
  let I : Ideal (𝓞 L) := Ideal.span {π ^ 2}
  have : Finite (𝓞 L ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 2 hπ.ne_zero))
  set K := Kg L N π r; set H := Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2
  let lift (x : K) : SpecialLinearGroup (Fin N) (𝓞 L) := Classical.choose x.2
  have : Finite (K ⧸ H.subgroupOf K) := Finite.of_injective
    (fun q : K ⧸ H.subgroupOf K => (Ideal.Quotient.mk I).mapMatrix (lift q.out : Matrix (Fin N) (Fin N) (𝓞 L)))
    fun q₁ q₂ hφ => by
      change (Ideal.Quotient.mk I).mapMatrix (lift q₁.out : Matrix (Fin N) (Fin N) (𝓞 L)) =
        (Ideal.Quotient.mk I).mapMatrix (lift q₂.out : Matrix (Fin N) (Fin N) (𝓞 L)) at hφ
      set c : SpecialLinearGroup (Fin N) L := q₁.out.1⁻¹ * q₂.out.1
      set γ : SpecialLinearGroup (Fin N) (𝓞 L) := (lift q₁.out)⁻¹ * lift q₂.out
      have hγ : dg L N π r * mt L N c = mo L N γ * dg L N π r := by
        have h1 : mo L N (lift q₁.out) * (dg L N π r * mt L N c) = mo L N (lift q₂.out) * dg L N π r := by
          rw [← Matrix.mul_assoc, ← Classical.choose_spec q₁.out.2, Matrix.mul_assoc, ← map_mul,
            mul_inv_cancel_left, Classical.choose_spec q₂.out.2]
        simpa [γ, ← Matrix.mul_assoc, ← map_mul] using congrArg (mo L N (lift q₁.out)⁻¹ * ·) h1
      have hmod : (Ideal.Quotient.mk I).mapMatrix (γ : Matrix (Fin N) (Fin N) (𝓞 L)) = 1 := by
        simp only [γ, SpecialLinearGroup.coe_mul, map_mul, ← hφ]
        rw [← map_mul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, map_one]
      have hs (s : ℕ) : c ∈ Kg L N π s := by
        rw [mem_Kg_iff hπ0]; intro i j
        have hij : (if (i : ℕ) < r then (π : L) else 1) * c i j = γ i j * if (j : ℕ) < r then (π : L) else 1 := by
          simpa [dg, mt, mo, diagonal_mul, mul_diagonal] using congrFun (congrFun hγ i) j
        have hdi : (if (i : ℕ) < r then (π : L) else 1) ≠ 0 := by split_ifs <;> simp [hπ0]
        by_cases hdiag : i = j
        · subst hdiag; exact ⟨γ i i, mul_left_cancel₀ hdi (by linear_combination (if (i : ℕ) < s then (π : L) else 1) * hij)⟩
        · obtain ⟨w, hw⟩ : π ^ 2 ∣ γ i j := by
            simpa [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, hdiag] using congrFun (congrFun hmod i) j
          refine ⟨w * (if (i : ℕ) < r then 1 else π) * (if (j : ℕ) < r then π else 1) *
            (if (i : ℕ) < s then π else 1) * (if (j : ℕ) < s then 1 else π), mul_left_cancel₀ hdi ?_⟩
          rw [mul_left_comm, hij, hw]; split_ifs <;> push_cast <;> ring
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ⟨⟨hs 0, hs 1⟩, hs 2⟩)
  exact Subgroup.index_ne_zero_of_finite

end

theorem arith_holds : Arith := by
  intro L _ _ π hπ hn N hN
  have hπ0 : (π : L) ≠ 0 := by simpa using (FaithfulSMul.algebraMap_injective (𝓞 L) L).ne hπ.ne_zero
  have hf0 := index_Kg_triple_ne_zero π hπ N 0
  let k0 : Fin N := ⟨0, by omega⟩; let k1 : Fin N := ⟨1, by omega⟩; let k2 : Fin N := ⟨2, by omega⟩
  have h01 : k0 ≠ k1 := by simp [k0, k1, Fin.ext_iff]
  have h21 : k2 ≠ k1 := by simp [k2, k1, Fin.ext_iff]
  exact
    { fin₀ := hf0, fin₁ := index_Kg_triple_ne_zero π hπ N 1, fin₂ := index_Kg_triple_ne_zero π hπ N 2
      two₀ := twoTr_Kg_of_iff hπ0 0 _ _ (col_twoTr π hπ h01) (mem_Kg_inf_succ_iff hπ0 (k := k0) rfl)
      two₁ := twoTr_Kg_of_iff hπ0 1 _ _ (col_twoTr π hπ h01.symm) (mem_Kg_inf_succ_iff hπ0 (k := k1) rfl)
      two₂ := twoTr_Kg_of_iff hπ0 2 _ _ (row_twoTr π hπ h01.symm) (mem_Kg_inf_succ_iff' hπ0 (k := k1) rfl)
      big₀₂ := hn.trans (absNorm_le_index_Kg hπ0 2 1 h01.symm (by simp [k1]) (by simp [k0]) (by simp [k1]) inf_le_right (fun _ h => h.1.2) hf0)
      big₀₁ := hn.trans (absNorm_le_index_Kg hπ0 1 2 h21 (by simp [k1]) (by simp [k1]) (by simp [k2]) (fun _ h => h.1.2) inf_le_right hf0) }

end PositivityTheory.KB.SpectralGap
