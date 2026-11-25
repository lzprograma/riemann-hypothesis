module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.LegendreSymbol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {τ r r' : K}

private def phiK (τ r : K) (h : r * r = -1 + τ * r) : Etau K τ →ₐ[K] K :=
  QuadraticAlgebra.lift ⟨r, by simpa using h⟩

private lemma phiK_apply (h : r * r = -1 + τ * r) (x : Etau K τ) :
    phiK τ r h x = x.re + x.im * r := by
  change x.re • (1 : K) + x.im • r = _
  simp

private lemma phiK_star (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : Etau K τ) :
    phiK τ r h (star x) = phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private lemma phiK_norm (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (hp : r * r' = 1)
    (x : Etau K τ) : QuadraticAlgebra.norm x = phiK τ r h x * phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.norm_def]
  linear_combination (-(x.re * x.im)) * hs - x.im ^ 2 * hp

private lemma phiK_ne (h : r * r = -1 + τ * r) (x : (Etau K τ)ˣ) : phiK τ r h (x : Etau K τ) ≠ 0 :=
  (x.isUnit.map (phiK τ r h)).ne_zero

private lemma phiK_quo (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : (Etau K τ)ˣ) :
    phiK τ r h (quo x) = phiK τ r h (x : Etau K τ) * (phiK τ r' h' (x : Etau K τ))⁻¹ := by
  rw [quo, map_mul, phiK_star h h' hs, map_units_inv]

private def phiEquiv (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') :
    Etau K τ ≃ₐ[K] K × K where
  toFun := (phiK τ r h).prod (phiK τ r' h')
  invFun p := ⟨p.1 - (p.1 - p.2) / (r - r') * r, (p.1 - p.2) / (r - r')⟩
  left_inv x := by
    have := sub_ne_zero.2 hne
    ext
    · simp only [AlgHom.prod_apply, phiK_apply]; field_simp; ring
    · simp only [AlgHom.prod_apply, phiK_apply]; field_simp; ring
  right_inv p := by
    have := sub_ne_zero.2 hne
    ext
    · simp [phiK_apply]
    · simp only [AlgHom.prod_apply, phiK_apply]; field_simp; ring
  map_mul' := ((phiK τ r h).prod (phiK τ r' h')).map_mul
  map_add' := ((phiK τ r h).prod (phiK τ r' h')).map_add
  commutes' := ((phiK τ r h).prod (phiK τ r' h')).commutes

private lemma phiK_int (O : Type) [CommRing O] [Algebra O K]
    (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (x : Etau K τ) :
    IsIntegral O x ↔ IsIntegral O (phiK τ r h x) ∧ IsIntegral O (phiK τ r' h' x) := by
  rw [← isIntegral_algEquiv ((phiEquiv h h' hne).restrictScalars O), IsIntegral.pair_iff]
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.evenValuation_norm_compactUnits_of_split :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → IsSquare (τ ^ 2 - 4) → (∀ c ∈ Cint O τ, EvenVal O (QuadraticAlgebra.norm ((c : (Etau K τ)ˣ) : Etau K τ))) ∧ ∀ y : (Etau K τ)ˣ, EvenVal O (QuadraticAlgebra.norm (y : Etau K τ)) → ∃ z : (Etau K τ)ˣ, ∃ c ∈ Cint O τ, y = c * z ^ 2 := by
  intro O K _ _ _ _ _ Δ τ hL hτ hsq
  haveI := hL.frac
  have h2 : (2 : K) ≠ 0 := by
    have e := (hL.two).map (algebraMap O K)
    rw [map_ofNat] at e
    exact e.ne_zero
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs, mul_zero]
  set r : K := (τ + s) / 2 with hrE
  set r' : K := (τ - s) / 2 with hr'E
  have hr : r * r = -1 + τ * r := by
    rw [hrE]
    field_simp
    linear_combination (-1 : K) * hs
  have hr' : r' * r' = -1 + τ * r' := by
    rw [hr'E]
    field_simp
    linear_combination (-1 : K) * hs
  have hsum : r + r' = τ := by
    rw [hrE, hr'E]
    field_simp
    ring
  have hsum' : r' + r = τ := by rw [add_comm]; exact hsum
  have hprod : r * r' = 1 := by
    rw [hrE, hr'E]
    field_simp
    linear_combination hs
  have hne : r ≠ r' := by
    intro e
    apply hs0
    have e2 : r - r' = s := by
      rw [hrE, hr'E]
      field_simp
      ring
    rw [← e2, e, sub_self]
  have hint : ∀ v : K, (∃ w : O, algebraMap O K w = v) → IsIntegral O v := by
    rintro v ⟨w, rfl⟩
    exact isIntegral_algebraMap
  have huv : ∀ (u : Oˣ) (v : K), v = algebraMap O K (u : O) → IsIntegral O v ∧ IsIntegral O v⁻¹ := by
    intro u v hv
    refine ⟨hint v ⟨u, hv.symm⟩, hint v⁻¹ ⟨(u⁻¹ : Oˣ), ?_⟩⟩
    rw [hv, map_units_inv]
  have hcint : ∀ (c : (Etau K τ)ˣ) (u : Oˣ),
      phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹ = algebraMap O K (u : O) →
      c ∈ Cint O τ := by
    intro c u hu
    obtain ⟨i1, i2⟩ := huv u _ hu
    have e2 : phiK τ r' hr' (c : Etau K τ) * (phiK τ r hr (c : Etau K τ))⁻¹
        = (phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹)⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm]
    refine ⟨?_, ?_⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', e2]
      exact ⟨i1, i2⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', map_units_inv,
        map_units_inv, inv_inv, inv_inv]
      refine ⟨?_, ?_⟩
      · rw [mul_comm, e2]
        exact i2
      · rw [mul_comm]
        exact i1
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨hc1, -⟩ := hc
    rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum'] at hc1
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.1
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.2
    have hA := phiK_ne hr c
    have hB := phiK_ne hr' c
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, phiK τ r' hr' (c : Etau K τ), hB, ?_⟩
    rw [phiK_norm hr hr' hsum hprod, Units.val_mk, ha]
    field_simp
  · rintro y ⟨u, t, ht, hy⟩
    have hA := phiK_ne hr y
    have hB := phiK_ne hr' y
    let z : (Etau K τ)ˣ :=
      Units.map (phiEquiv hr hr' hne).symm.toMonoidHom
        (MulEquiv.prodUnits.symm (1, Units.mk0 _ (div_ne_zero hB ht)))
    have hz := (phiEquiv hr hr' hne).apply_symm_apply (1, phiK τ r' hr' (y : Etau K τ) / t)
    have hz1 : phiK τ r hr (z : Etau K τ) = 1 := congrArg Prod.fst hz
    have hz2 : phiK τ r' hr' (z : Etau K τ) = phiK τ r' hr' (y : Etau K τ) / t :=
      congrArg Prod.snd hz
    refine ⟨z, y * (z ^ 2)⁻¹, ?_, (inv_mul_cancel_right y (z ^ 2)).symm⟩
    apply hcint _ u
    rw [Units.val_mul, map_mul, map_mul, map_units_inv, map_units_inv, Units.val_pow_eq_pow_val,
      map_pow, map_pow, hz1, hz2]
    have hn := phiK_norm hr hr' hsum hprod (y : Etau K τ)
    rw [hy] at hn
    field_simp
    linear_combination (-1 : K) * hn
