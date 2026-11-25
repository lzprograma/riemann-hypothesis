module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem finsum_maximalSpectrum_ord_eq_sum {O B ι : Type*} [CommRing O] [CommRing B] [Algebra O B] (θ : B)
    (S : Finset ι) (c : ι → Ideal B) (hc : Set.BijOn c ↑S {P | P.IsMaximal ∧ θ ∈ P}) (m : ι → ℕ∞)
    (hm : ∀ i ∈ S, ∀ _ : (c i).IsPrime,
      Ring.ord (Localization.AtPrime (c i)) (algebraMap B _ θ) * Module.length O (B ⧸ c i) = m i) :
    ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal) =
      ∑ i ∈ S, m i := by
  classical
  let ψ : Ideal B → ℕ∞ := fun P => if h : P.IsMaximal then
    (haveI := h.isPrime
     Ring.ord (Localization.AtPrime P) (algebraMap B (Localization.AtPrime P) θ) * Module.length O (B ⧸ P))
    else 0
  calc ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)
      = ∑ᶠ 𝔓 ∈ {𝔓 : MaximalSpectrum B | θ ∈ 𝔓.asIdeal},
          Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) *
            Module.length O (B ⧸ 𝔓.asIdeal) := by
        refine finsum_congr fun 𝔓 => ?_
        rw [finsum_eq_if]
        split_ifs with h
        · rfl
        · have hu : IsUnit (algebraMap B (Localization.AtPrime 𝔓.asIdeal) θ) :=
            IsLocalization.map_units (M := 𝔓.asIdeal.primeCompl) (Localization.AtPrime 𝔓.asIdeal) ⟨θ, h⟩
          rw [Ring.ord_of_isUnit hu, zero_mul]
    _ = ∑ᶠ P ∈ {P : Ideal B | P.IsMaximal ∧ θ ∈ P}, ψ P :=
        finsum_mem_eq_of_bijOn MaximalSpectrum.asIdeal
          ⟨fun 𝔓 h => ⟨𝔓.isMaximal, h⟩, fun a _ b _ h => MaximalSpectrum.ext h,
            fun P hP => ⟨⟨P, hP.1⟩, hP.2, rfl⟩⟩
          (fun 𝔓 _ => by simp only [ψ, dite_eq_left 𝔓.isMaximal])
    _ = ∑ᶠ i ∈ (S : Set ι), ψ (c i) := (finsum_mem_eq_of_bijOn c hc fun _ _ => rfl).symm
    _ = ∑ i ∈ S, ψ (c i) := finsum_mem_coe_finset _ _
    _ = ∑ i ∈ S, m i := Finset.sum_congr rfl fun i hi => by
        have hmax : (c i).IsMaximal := (hc.mapsTo (Finset.mem_coe.mpr hi)).1
        simp only [ψ, dite_eq_left hmax]
        exact hm i hi hmax.isPrime

open Classical in
theorem ChartLength.proof_of_residueDegree
    {F : Type} [Field F] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin (e + 1) × Fin n) F} {t u : Fin n → F}
    {q : MvPolynomial (Fin e × Fin n) F} {p : Ideal (MvPolynomial (Fin e × Fin n) F)}
    [p.IsPrime] (hI : IsProjPrime I) (hf : IsChowForm I (e + 1) f) (hu : linForm u ∉ I)
    (hq : Prime q) (hp : p = Ideal.span {q}) (hqt : ¬q ∣ specFirst f t)
    (h₂ : SpecFirstMemIncIdeal.Statement) (h₃ : ChartFinite.Statement)
    (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement)
    (h₇ : ∀ W, W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e → linForm t ∉ W →
      Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ chartIdeal I t e p W) = 1) :
    Module.length (Localization.AtPrime p)
        (ChartLoc I t e p ⧸ LinearMap.range (LinearMap.mulLeft (Localization.AtPrime p)
          (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
      ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e, ((divCycle I u W : ℕ) : ℕ∞) := by
  classical

  have hpt : specFirst f t ∉ p := by
    rw [hp, Ideal.mem_span_singleton]
    exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₃ F n e I f t p hI hf hpt
  rw [h₄ (Localization.AtPrime p) (ChartLoc I t e p)
    (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]
  refine finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_
  · have h := h₅ F n e I f t u q p hI hf hu hq hp hqt
    convert h using 1
    ext W
    simp
  · intro W hW _
    obtain ⟨hWs, hWq⟩ := Finset.mem_filter.mp hW
    have hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
      rw [Finsupp.mem_support_iff] at hWs
      by_contra h
      exact hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
    have hqW : q ∈ incIdeal W e := hWq ▸ Ideal.mem_span_singleton_self q
    have htW : linForm t ∉ W := fun h => by
      have hIW : I ≤ W := le_trans le_sup_left hrel.1.1.2
      have := h₂ F n e I W f t hf hIW h
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    obtain ⟨_, hord⟩ := h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hlen := h₇ W hrel hqW htW
    have hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W := by
      simp [divCycle, fundCycle, Finsupp.onFinset_apply, hrel]
    rw [hlen, mul_one, hdiv]
    exact hord

theorem ChartLength.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegree.Statement) : ChartLength.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  exact ChartLength.proof_of_residueDegree hI hf hu hq hp hqt h₂ h₃ h₄ h₅ h₆
    (fun W => h₇ F n e I W f t u q p hI hf hu hq hp hqt)

open Classical in
theorem SectionOrder.proof_of_chart
    {F : Type} [Field F] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin (e + 1) × Fin n) F} {u : Fin n → F}
    (hI : IsProjPrime I) (hf : IsChowForm I (e + 1) f) (hu : linForm u ∉ I)
    (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ∀ q : MvPolynomial (Fin e × Fin n) F, Prime q → ∃ t : Fin n → F, ¬q ∣ specFirst f t)
    (hne : specFirst f u ≠ 0) (h₅ : LocalizationPrimeDVR.Statement)
    (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement) (h₈ : ChartLocDomain.Statement)
    (h₉ : ∀ (t : Fin n → F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
      (p = ⊥ ∨ ∃ q, Prime q ∧ p = Ideal.span {q}) → specFirst f t ∉ p →
      algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (specFirst f u) =
        algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (specFirst f t) *
          LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
            (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))))
    (h₁₀ : ∀ (t : Fin n → F) (q : MvPolynomial (Fin e × Fin n) F)
      (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
      Prime q → p = Ideal.span {q} → ¬q ∣ specFirst f t →
      Module.length (Localization.AtPrime p)
          (ChartLoc I t e p ⧸ LinearMap.range (LinearMap.mulLeft (Localization.AtPrime p)
            (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
        ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e, ((divCycle I u W : ℕ) : ℕ∞))
    (h₁₁ : LengthQuotientDet.Statement) :
    specFirst f u ≠ 0 ∧ ∀ q : MvPolynomial (Fin e × Fin n) F, Irreducible q →
      emultiplicity q (specFirst f u) =
        ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e, ((divCycle I u W : ℕ) : ℕ∞) := by
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ q hqp
  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ t p (Or.inr ⟨q, hqp, rfl⟩) htp
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ t q p hqp rfl ht

end

end GroundTheory.Heights₂.Heights
