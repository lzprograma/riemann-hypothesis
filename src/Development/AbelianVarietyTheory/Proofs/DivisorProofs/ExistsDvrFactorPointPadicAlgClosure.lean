module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing GlobalTheory.ZH
  ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ValPt.exists_dvr_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ y : Sp (OO p) ⟶ M.Z, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (fV : V →+* V') (fK : FractionRing V →+* FractionRing V') (κ' : FractionRing V' →+* PadicAlgCl p) (iV : V' →+* OO p) (ξ : Sp V' ⟶ M.Z), IsLocalHom fV ∧ (∀ x, fK (algebraMap V _ x) = algebraMap V' _ (fV x)) ∧ κ'.comp fK = κ ∧ IsLocalHom iV ∧ (∀ x, (iV x : PadicAlgCl p) = κ' (algebraMap V' _ x)) ∧ spMap iV ≫ ξ = y := by
  intro o Ω _ _ _ _ M p _ V _ _ _ hc κ hV y
  have : CharZero V := (κ.comp (algebraMap V (FractionRing V))).charZero
  set x : M.Z := y (cPt p)
  obtain ⟨φ, -, hφ, -⟩ := GlobalTheory.ValPt.exists_unique_stalk_hom M.Z x p y rfl
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.RatModel.exists_affineOpen_finiteType_int o Ω M x
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  let y₀ : Γ(M.Z, U) →+* PadicAlgCl p :=
    (OO p).subtype.comp (φ.comp (M.Z.presheaf.germ U x hxU).hom)
  obtain ⟨W, _, _, _, -, _, fV, fK, κ', -, hfVloc, -, hfK, hκ', hW, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ Γ(M.Z, U) y₀
  let j : W →+* PadicAlgCl p := κ'.comp (algebraMap W (FractionRing W))
  have hj : Function.Injective j :=
    κ'.injective.comp (IsFractionRing.injective W (FractionRing W))
  let ψ : M.Z.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ
  have hψK : ∀ s, ψ s ∈ κ'.range := fun s => by
    let xU : U := ⟨x, hxU⟩
    let := M.Z.presheaf.algebra_section_stalk xU
    have := hU.isLocalization_stalk xU
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf xU).asIdeal.primeCompl
      (show M.Z.presheaf.stalk (xU : M.Z) from s)
    have hb : y₀ b ≠ 0 :=
      (((IsLocalization.map_units _ b).map φ).map (OO p).subtype).ne_zero
    obtain ⟨ka, hka⟩ := hy₀ a
    obtain ⟨kb, hkb⟩ := hy₀ b
    refine ⟨ka * kb⁻¹, ?_⟩
    have e1 : ψ s * y₀ b = y₀ a := by
      change ψ s * ψ (algebraMap Γ(M.Z, U) _ _) = ψ (algebraMap Γ(M.Z, U) _ _)
      rw [← map_mul, hab]
    rw [map_mul, map_inv₀, hka, hkb, ← e1, mul_inv_cancel_right₀ hb]
  have hψW : ∀ s, ψ s ∈ j.range := fun s => by
    obtain ⟨k, hk⟩ := hψK s
    obtain ⟨w, hw⟩ := (hW k).1 (hk ▸ (mem_OO_iff _).1 (φ s).2)
    exact ⟨w, by simpa [j, hw] using hk⟩
  let e := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let φ' : M.Z.presheaf.stalk x →+* W := e.symm.toRingHom.comp (ψ.codRestrict j.range hψW)
  let iV : W →+* OO p := j.codRestrict (OO p) fun w => (mem_OO_iff _).2 ((hW _).2 ⟨w, rfl⟩)
  have hiVloc : IsLocalHom iV := ⟨fun w ⟨u, hu⟩ => by
    have hu_mul : (((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p) * j w = 1 := by
      simpa [iV, hu] using congrArg (OO p).subtype u.inv_val
    have hwne : algebraMap W (FractionRing W) w ≠ 0 :=
      fun h => right_ne_zero_of_mul_eq_one hu_mul (by simp [j, h])
    have hinv : ‖κ' (algebraMap W (FractionRing W) w)⁻¹‖ ≤ 1 := by
      rw [map_inv₀]
      change ‖(j w)⁻¹‖ ≤ 1
      rw [← eq_inv_of_mul_eq_one_left hu_mul]
      exact (mem_OO_iff _).1 (u⁻¹ : (OO p)ˣ).1.2
    obtain ⟨w', hw'⟩ := (hW _).1 hinv
    exact IsUnit.of_mul_eq_one w' <| IsFractionRing.injective W (FractionRing W) <| by
      rw [map_mul, hw', map_one, mul_inv_cancel₀ hwne]⟩
  have hcomp : iV.comp φ' = φ := by
    ext s
    exact congrArg (Subtype.val : j.range → _) (e.apply_symm_apply (ψ.codRestrict j.range hψW s))
  refine ⟨W, inferInstance, inferInstance, inferInstance, fV, fK, κ', iV,
    spMap φ' ≫ M.Z.fromSpecStalk x, hfVloc, hfK, hκ', hiVloc, fun _ => rfl, ?_⟩
  rw [← Category.assoc, ← hφ, ← hcomp]
  exact congrArg (· ≫ M.Z.fromSpecStalk x) (Spec.map_comp _ _).symm
