module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartFirstGroupDvd
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncDomain
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncidenceGeneric
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartFirstGroupDvd

theorem dvd_sub_aeval {R : Type*} [CommRing R] {n : ℕ} (a : MvPolynomial (Fin n) R)
    (σ : Fin n → MvPolynomial (Fin n) R) (hσ : ∀ m, a ∣ σ m - X m) (P : MvPolynomial (Fin n) R) :
    a ∣ P - aeval σ P := by
  set π := Ideal.Quotient.mk (Ideal.span {a})
  have h : π.comp (aeval σ).toRingHom = π := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π]
    · intro m
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, π]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hσ m
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  exact (RingHom.congr_fun h P).symm

variable {F : Type} [Field F] {n : ℕ}

theorem exists_injective (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (t : Fin n → F) (e : ℕ)
    (hI : IsProjPrime I) (ht : linForm t ∉ I) :
    ∃ φ : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I)),
      Function.Injective φ ∧
      (∀ g, φ (chartX I t e g) = C (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) g)) ∧
      ∀ im, φ (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im)) =
        genSubst ((aeval (genPt I) (linForm t))⁻¹ • genPt I)
          (fun m => algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m)) im := by
  set K := FractionRing (MvPolynomial (Fin n) F ⧸ I)
  set η : Fin n → K := (aeval (genPt I) (linForm t))⁻¹ • genPt I with hη
  set ψ : MvPolynomial (Fin n) F →+* K := (aeval η).toRingHom with hψ
  have hJeq : RingHom.ker ψ = I ⊔ Ideal.span {linForm t - 1} := by
    rw [← ChartIncDomain.ker_aeval_eta I t hI ht]
    rfl
  obtain ⟨γbar, hinj, hγX, hγU⟩ := ChartIncDomain.exists_embed I t e
  let eJ : MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {linForm t - 1}) ≃+*
      MvPolynomial (Fin n) F ⧸ RingHom.ker ψ := Ideal.quotEquivOfEq hJeq.symm
  let κ : MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {linForm t - 1}) →+* K :=
    (RingHom.kerLift ψ).comp eJ.toRingHom
  have hκinj : Function.Injective κ := (RingHom.kerLift_injective ψ).comp eJ.injective
  have hκmk : ∀ g, κ (Ideal.Quotient.mk _ g) = ψ g := fun g => by
    show RingHom.kerLift ψ (Ideal.Quotient.mk (RingHom.ker ψ) g) = ψ g
    exact RingHom.kerLift_mk ψ g
  refine ⟨(MvPolynomial.map κ).comp γbar, (map_injective _ hκinj).comp hinj, ?_, ?_⟩
  · intro g
    simp only [RingHom.comp_apply, hγX, map_C, hκmk, hψ]
    rfl
  · intro im
    simp only [RingHom.comp_apply, hγU, IncidenceGeneric.map_genSubst]
    congr 1 <;> funext m <;> rw [hκmk, hψ]
    · simp [η]
    · simp; rfl

theorem proof (h₁ : IncidenceGeneric.Statement) : ChartFirstGroupDvd.Statement := by
  intro F _ n e I f t hI hf ht
  have := hI.isPrime
  obtain ⟨φ, hφinj, hφX, hφU⟩ := exists_injective I t e hI ht
  set τ : (FractionRing (MvPolynomial (Fin n) F ⧸ I)) := aeval (genPt I) (linForm t) with hτdef
  have hτ : τ ≠ 0 := by
    rw [hτdef, ChartIncDomain.aeval_genPt, Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ht
  have hτsum : τ = ∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t l) * genPt I l := by
    simp [hτdef, linForm]
  set cK : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ I)) := fun m => algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m) / τ with hcK
  have homogComponent_comm_first_action : ∑ j, cK j * genPt I j = 1 := by
    simp only [hcK, div_mul_eq_mul_div, ← Finset.sum_div, ← hτsum]
    exact div_self hτ
  have hcKm : ∀ m, cK m = τ⁻¹ * algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m) := fun m => by
    simp only [hcK]
    ring
  have hfI : f ∈ incIdeal I (e + 1) := mem_incIdeal_iff.mpr ((hf.2 f).mpr dvd_rfl)
  have hgen : aeval (genSubst (genPt I) cK) f = 0 := (h₁ F n (e + 1) I cK homogComponent_comm_first_action f).mp hfI
  set θ : MvPolynomial (Fin n) (ChartInc I t e) := ∑ m, X m * C (chartX I t e (X m)) with hθ
  set σ : Fin n → MvPolynomial (Fin n) (ChartInc I t e) :=
    fun m => X m - θ * C (chartX I t e (C (t m))) with hσ
  have hdvd := dvd_sub_aeval θ σ (fun m => ⟨-C (chartX I t e (C (t m))), by simp only [hσ]; ring⟩)
    (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f))
  suffices h0 : aeval σ (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f)) = 0 by
    rw [h0, sub_zero] at hdvd
    exact hdvd
  apply map_injective φ hφinj
  rw [map_zero]
  set ρ : MvPolynomial (Fin (e + 1) × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I)) →+* MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))) :=
    eval₂Hom (C.comp C) (fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))))
      (X ij.2) (fun i => C (X (i, ij.2))) ij.1) with hρ
  have key : (MvPolynomial.map φ).comp ((aeval σ).toRingHom.comp
      ((MvPolynomial.map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e))).comp
        (aeval (fun ij : Fin (e + 1) × Fin n =>
          Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
            (X ij.2) (fun i => C (X (i, ij.2))) ij.1)).toRingHom)) =
      ρ.comp (aeval (genSubst (genPt I) cK) :
        MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin (e + 1) × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))).toRingHom := by
    have hρ0 : ∀ m, ρ (X (0, m)) = X m := fun m => by simp [hρ]
    have hρs : ∀ (i : Fin e) m, ρ (X (i.succ, m)) = C (X (i, m)) := fun i m => by simp [hρ]
    have hρC : ∀ k, ρ (C k) = C (C k) := fun k => by simp [hρ]
    apply MvPolynomial.ringHom_ext
    · intro a
      have hCa : algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) = chartX I t e (C a) := by
        change Ideal.Quotient.mk _ (rename Sum.inr (C a)) = Ideal.Quotient.mk _ (rename Sum.inl (C a))
        rw [rename_C, rename_C]
      simp [hρC, hCa, hφX]
    · rintro ⟨i, m⟩
      cases i using Fin.cases with
      | zero =>
        simp [hρ0, hσ, hθ, hφX, hρC, genSubst]
        rw [hcKm]
        simp only [map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      | succ i =>
        simp [hρs, hρC, hφU, genSubst]
        rw [hcKm]
        simp only [map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hgen, map_zero] at this
  exact this

end ChartFirstGroupDvd

end

end GroundTheory.Heights₂.Heights
