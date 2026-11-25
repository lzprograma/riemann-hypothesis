module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace Gp91

namespace GlobalTheory.DSInequiv

private lemma dsParamUniq_conj_mem {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r}
    (hu : IsUnit P) (hP : Pᴴ * PI.UpqRep.Jm ε * P = PI.UpqRep.Hpk k r) {g : Mx k r} (hg : g ∈ PI.UpqRep.UJset ε) :
    P⁻¹ * g * P ∈ GG k r := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hu
  have hPi : (P⁻¹)ᴴ * PI.UpqRep.Hpk k r * P⁻¹ = PI.UpqRep.Jm ε := by
    rw [← hP, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, ← Matrix.mul_assoc, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hd, conjTranspose_one, Matrix.one_mul]
  change (P⁻¹ * g * P)ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * g * P) = PI.UpqRep.Hpk k r
  calc _ = Pᴴ * (gᴴ * ((P⁻¹)ᴴ * PI.UpqRep.Hpk k r * P⁻¹) * g) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * P := by rw [hPi]
    _ = Pᴴ * PI.UpqRep.Jm ε * P := by rw [hg]
    _ = _ := hP

private lemma dsParamUniq_exists_kfin {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    (R : Rep k r) {P : Mx k r} (hP : PI.UpqRep.IsCayleyU k r ε P)
    (h : PI.UpqRep.IsDS ε mu (fun g => R.σ (P⁻¹ * g * P))) : ∃ v : R.H, R.KFin v ∧ v ≠ 0 := by
  obtain ⟨S, hfin, hst, -, ⟨w, hwS, hw0, -⟩, -⟩ := h.2.2.2.2.2.1
  refine ⟨w, ⟨S, hfin, hwS, fun g hg x hx => ?_⟩, hw0⟩
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have h1 : P * Pᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hPu
  have h2 : Pᴴ * P = 1 := (Matrix.mem_unitaryGroup_iff').mp hPu
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv h2
  have hgu : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hg.2
  have hg1 : g * gᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hgu
  have hgH : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg.1
  have hcom : PI.UpqRep.Hpk k r * g = g * PI.UpqRep.Hpk k r := by
    calc PI.UpqRep.Hpk k r * g = (g * gᴴ) * PI.UpqRep.Hpk k r * g := by rw [hg1, Matrix.one_mul]
      _ = g * (gᴴ * PI.UpqRep.Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = g * PI.UpqRep.Hpk k r := by rw [hgH]
  have hJ : PI.UpqRep.Jm ε = P * PI.UpqRep.Hpk k r * Pᴴ := by
    rw [← hP.1.2]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hK : P * g * P⁻¹ ∈ PI.UpqRep.Kset ε := by
    refine ⟨?_, ?_⟩
    · rw [hinv]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPu hgu) (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_eq_conjTranspose, conjTranspose_conjTranspose, h2]))
    · rw [hinv, hJ]
      calc P * g * Pᴴ * (P * PI.UpqRep.Hpk k r * Pᴴ) = P * (g * PI.UpqRep.Hpk k r) * Pᴴ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Pᴴ P, h2, Matrix.one_mul]
        _ = P * (PI.UpqRep.Hpk k r * g) * Pᴴ := by rw [hcom]
        _ = P * PI.UpqRep.Hpk k r * Pᴴ * (P * g * Pᴴ) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Pᴴ P, h2, Matrix.one_mul]
  have : R.σ (P⁻¹ * (P * g * P⁻¹) * P) x ∈ S := hst _ hK x hx
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have e : P⁻¹ * (P * g * P⁻¹) * P = g := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hdP, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdP, Matrix.one_mul]
  rwa [e] at this

section Smooth

open scoped Matrix.Norms.Elementwise

private theorem dsParamUniq_smoothOn_comp {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H J A B : Matrix (Fin n) (Fin n) ℂ} (hAB : ∀ g, gᴴ * J * g = J → (A * g * B)ᴴ * H * (A * g * B) = H)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : PI.UpqRep.SmoothOnH H f) :
    PI.PhMeasCore.SmoothOnH J (fun g => f (A * g * B)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, he⟩ := hf (A * g₀ * B) (hAB g₀ hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => A * g * B
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let L' := LinearMap.toContinuousLinearMap L
  refine ⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, ?_, ?_⟩
  · exact hF.comp L'.contDiff.contDiffOn (fun x hx => hx)
  · intro g hg hgJ
    exact he (A * g * B) hg (hAB g hgJ)

end Smooth

private lemma dsParamUniq_smooth_conj {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (R : Rep k r) {P : Mx k r}
    (hu : IsUnit P) (hP : Pᴴ * PI.UpqRep.Jm ε * P = PI.UpqRep.Hpk k r) {v : R.H} (hv : v ∈ R.sm) :
    v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (P⁻¹ * g * P)) :=
  dsParamUniq_smoothOn_comp (H := PI.UpqRep.Hpk k r) (f := fun g => R.σ g v)
    (fun g hg => dsParamUniq_conj_mem hu hP (g := g) hg) hv

private lemma dsParamUniq_cayley_quot {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P Q : Mx k r}
    (hQ : IsUnit Q) (hP : Pᴴ * PI.UpqRep.Jm ε * P = PI.UpqRep.Hpk k r)
    (hQ' : Qᴴ * PI.UpqRep.Jm ε * Q = PI.UpqRep.Hpk k r) : P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  change (P * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  calc _ = (Q⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * Q⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Q⁻¹)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q) * Q⁻¹ := by rw [hP, hQ']
    _ = _ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, ← Matrix.mul_assoc,
          ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one,
          Matrix.one_mul]

private lemma dsParamUniq_inUJ_mul {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ PI.UpqRep.UJset ε) (hb : b ∈ PI.UpqRep.UJset ε) : a * b ∈ PI.UpqRep.UJset ε := by
  have ha' : aᴴ * PI.UpqRep.Jm ε * a = PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * PI.UpqRep.Jm ε * b = PI.UpqRep.Jm ε := hb
  change (a * b)ᴴ * PI.UpqRep.Jm ε * (a * b) = PI.UpqRep.Jm ε
  calc _ = bᴴ * (aᴴ * PI.UpqRep.Jm ε * a) * b := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

private lemma dsParamUniq_eq_of_capP {n : ℕ} (mu mu' : Fin n → ℝ) (hm : StrictAnti mu) (hm' : StrictAnti mu')
    (h : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y =
      Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y) : mu = mu' := by
  have key : ∀ (f : Fin n → ℝ) (x : ℝ),
      Formalism.QuantumDeterminants.capP (fun s => (f s : ℂ)) (-(x : ℂ)) = 0 ↔ x ∈ Set.range f := by
    intro f x
    unfold Formalism.QuantumDeterminants.capP
    rw [Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨s, -, hs⟩
      refine ⟨s, ?_⟩
      have : ((f s : ℝ) : ℂ) = (x : ℂ) := by linear_combination hs
      exact_mod_cast this
    · rintro ⟨s, rfl⟩
      exact ⟨s, Finset.mem_univ _, by ring⟩
  have hr : Set.range mu = Set.range mu' := by
    ext x
    rw [← key, ← key, h]
  have hs : StrictMono (mu ∘ Fin.rev) := fun a b hab => hm (Fin.rev_lt_rev.mpr hab)
  have hs' : StrictMono (mu' ∘ Fin.rev) := fun a b hab => hm' (Fin.rev_lt_rev.mpr hab)
  have hr' : Set.range (OrderEmbedding.ofStrictMono _ hs) = Set.range (OrderEmbedding.ofStrictMono _ hs') := by
    simp only [OrderEmbedding.coe_ofStrictMono, Set.range_comp, Fin.range_rev, Set.image_univ]
    exact hr
  have e := OrderEmbedding.range_inj_of_wellFoundedLT.mp hr'
  funext a
  have := DFunLike.congr_fun e (Fin.rev a)
  simpa using this

section Equiv

open scoped Matrix.Norms.Elementwise

variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

private lemma dsParamUniq_smooth_equiv (V : H ≃L[ℂ] H')
    (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x)) {v : H}
    (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) :
    V v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, he⟩ := hv g₀ hg₀
  refine ⟨U, (_root_.GlobalTheory.DSInequiv.toReal V) ∘ F, hU, hm,
    (_root_.GlobalTheory.DSInequiv.toReal V).contDiff.comp_contDiffOn hF, fun g hg hgU => ?_⟩
  change τ' g (V v) = V (F g)
  rw [← hV g hgU]
  exact congrArg V (he g hg hgU)

private lemma dsParamUniq_inG_re (Y : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε ((1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y)) := by
  unfold Formalism.REAL.inG PI.DSInfCharCap.thetaJ
  have hJ := Formalism.REAL.Jm_conjTranspose ε
  have hJJ := Formalism.REAL.Jm_mul_self ε
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_mul, hJ,
    conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  convert smul_zero (1 / 2 : ℂ) using 2
  abel

private lemma dsParamUniq_inG_im (Y : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε ((1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y)) := by
  unfold Formalism.REAL.inG PI.DSInfCharCap.thetaJ
  have hJ := Formalism.REAL.Jm_conjTranspose ε
  have hJJ := Formalism.REAL.Jm_mul_self ε
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul, hJ,
    conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp
  rw [this, neg_smul]
  simp only [sub_neg_eq_add]
  rw [add_comm (Formalism.REAL.Jm ε * Y), neg_add_cancel]

private lemma dsParamUniq_dsigCW_equiv (V : H ≃L[ℂ] H')
    (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x)) (w : List (Matrix (Fin n) (Fin n) ℂ))
    (v : H) : V (PI.DSInfCharCap.dsigCW ε τ w v) = PI.DSInfCharCap.dsigCW ε τ' w (V v) := by
  induction w with
  | nil => rfl
  | cons Y w ih =>
    simp only [PI.DSInfCharCap.dsigCW, PI.DSInfCharCap.dsigC, map_add, map_smul]
    rw [_root_.GlobalTheory.DSInequiv.dsig_equiv V hV _ (dsParamUniq_inG_re Y),
      _root_.GlobalTheory.DSInequiv.dsig_equiv V hV _ (dsParamUniq_inG_im Y), ih]

private lemma dsParamUniq_actU_equiv (V : H ≃L[ℂ] H')
    (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x)) (p : FreeAlgebra ℂ (Fin n × Fin n))
    (v : H) : V (PI.DSInfCharCap.actU ε τ p v) = PI.DSInfCharCap.actU ε τ' p (V v) := by
  unfold PI.DSInfCharCap.actU
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [map_smul, dsParamUniq_dsigCW_equiv V hV]

end Equiv

theorem param_eq_of_equiv : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  intro hy k r ε mu mu' R R' hR hR' U hU
  obtain ⟨hm, ⟨P, hP, h⟩, hgp⟩ := hR
  obtain ⟨hm', ⟨Q, hQ, h'⟩, hgp'⟩ := hR'
  obtain ⟨v, hv, hv0⟩ := dsParamUniq_exists_kfin R hP h
  have hs := hy.1.2.2.1 k r ε mu R.H R.σ hm ⟨P, hP, h⟩ v hv
  have hs' := dsParamUniq_smooth_conj R hP.1.1 hP.1.2 hs
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hdQ := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  have p1 := Matrix.mul_nonsing_inv _ hdP
  have q1 := Matrix.mul_nonsing_inv _ hdQ
  have q2 := Matrix.nonsing_inv_mul _ hdQ
  have p3 := fun B : Mx k r => Matrix.nonsing_inv_mul_cancel_left P B hdP
  have q3 := fun B : Mx k r => Matrix.nonsing_inv_mul_cancel_left Q B hdQ
  have p4 := fun B : Mx k r => Matrix.mul_nonsing_inv_cancel_left P B hdP
  have ha := dsParamUniq_cayley_quot hQ.1.1 hP.1.2 hQ.1.2
  have hb := dsParamUniq_cayley_quot hP.1.1 hQ.1.2 hP.1.2
  obtain ⟨⟨hone, hmul⟩, -⟩ := h'.2.2.1
  set τ' : Mx k r → (R'.H →L[ℂ] R'.H) := fun g => R'.σ (Q⁻¹ * g * Q) with hτ'
  have hmul' : ∀ a ∈ PI.UpqRep.UJset ε, ∀ b ∈ PI.UpqRep.UJset ε, ∀ x, τ' a (τ' b x) = τ' (a * b) x :=
    fun a ha b hb x => (DFunLike.congr_fun (hmul a ha b hb) x).symm
  have hab : (P * Q⁻¹) * (Q * P⁻¹) = 1 := by simp only [Matrix.mul_assoc, q3, p1]
  have hba : (Q * P⁻¹) * (P * Q⁻¹) = 1 := by simp only [Matrix.mul_assoc, p3, q1]
  let A : R'.H ≃L[ℂ] R'.H := ContinuousLinearEquiv.ofContinuousLinearMap (τ' (P * Q⁻¹)) (τ' (Q * P⁻¹))
    (by ext x; exact (hmul' _ ha _ hb x).trans (by rw [hab, hone]; rfl))
    (by ext x; exact (hmul' _ hb _ ha x).trans (by rw [hba, hone]; rfl))
  have hVA : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, (U.toContinuousLinearEquiv.trans A) (R.σ (P⁻¹ * g * P) x) = τ' g ((U.toContinuousLinearEquiv.trans A) x) := by
    intro g hg x
    have hg' : g ∈ PI.UpqRep.UJset ε := hg
    have hG : P⁻¹ * g * P ∈ GG k r := dsParamUniq_conj_mem hP.1.1 hP.1.2 hg
    show τ' (P * Q⁻¹) (U (R.σ (P⁻¹ * g * P) x)) = τ' g (τ' (P * Q⁻¹) (U x))
    have e : R'.σ (P⁻¹ * g * P) = τ' (Q * P⁻¹ * g * (P * Q⁻¹)) := by
      simp only [hτ', Matrix.mul_assoc, q3, q2, Matrix.mul_one]
    rw [hU _ hG, e, hmul' _ ha _ (dsParamUniq_inUJ_mul (dsParamUniq_inUJ_mul hb hg') ha), hmul' _ hg' _ ha]
    simp only [Matrix.mul_assoc, q3, p4]
  refine dsParamUniq_eq_of_capP mu mu' hm.1 hm'.1 fun Y => ?_
  have e1 := hy.2.2.1 k r ε mu _ _ ⟨P, hP⟩ hgp hm h v hs' Y
  have e2 := hy.2.2.1 k r ε mu' _ _ ⟨P, hP⟩ hgp' hm' h' _ (dsParamUniq_smooth_equiv (U.toContinuousLinearEquiv.trans A) hVA hs') Y
  rw [← dsParamUniq_actU_equiv (U.toContinuousLinearEquiv.trans A) hVA, e1, map_smul] at e2
  exact smul_left_injective ℂ (by simpa using hv0) e2

end GlobalTheory.DSInequiv

end Gp91
