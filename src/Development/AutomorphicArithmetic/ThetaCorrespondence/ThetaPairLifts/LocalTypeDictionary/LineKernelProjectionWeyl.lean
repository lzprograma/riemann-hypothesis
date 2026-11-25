module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanProductRuleDerivative
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanThetaFamilyExistsSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesawStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposesStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LineDerivCore

theorem lift_splits_locally_core (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (D : D7) (θ : InfFam D) (X : HSp D)
    {a a' n : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Wsp : Spc D.host.F D.host.E (a + a')) (Vsp : Spc D.host.F D.host.E n)
    (M : Model D.sp.cm.sig Vsp Wsp) (χ₁ χ₂ : (AE D)ˣ →* Circle)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vsp Wsp)
    (hJ : Wsp.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hθ : IsInfFam θ) (hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig) (hstdB : IsStd Bs.ψ)
    (hM : M.IsGood Bs.ψ) (hweil : M.IsWeil Bs.ψ χ₁ χ₂ om)
    (l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ)) (hl : ∀ q ∈ l, q.2 ∈ lieAt X q.1)
    (f : SInf D.host.F (Fin n × Fin (a + a'))) (_hf : f ∈ M.Pol Bs.ψ Bs.emb)
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin n × Fin (a + a') → v.adicCompletion D.host.F) → ℂ)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v)
    (Ψ : Fin l.length → (Fin n × Fin (a + a') → AF D.host.F) → ℂ)
    (hΨ : ∀ i, Ψ i ∈ algD M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) x) (Ψ i x) 0)
    (x : Fin n × Fin (a + a') → AF D.host.F) :
    HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) x) (∑ i, Ψ i x) 0 := by
  classical
  have hline : ∀ i : Fin l.length, ∃ γ ∈ Lines D.sp.cm.sig Wsp, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t) := fun i =>
    GlobalTheory.KapXLine.exists_line D θ X (l.get i).1 (l.get i).2 hθ (hl _ (List.get_mem _ _)) e Wsp hJ
  choose γ hγ hγt using hline
  have hT := fun i => _root_.GlobalTheory.ArchFamily.exists_archimedean_theta_family hP M Bs.ψ χ₁ χ₂ om hcm hstdB hweil (γ i) (hγ i)
  choose T hTa hTadd hT0 using hT
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 := by
    filter_upwards [hvac, hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨r, hR, hpure⟩ : ∃ r : (Fin n × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ g : SInf D.host.F (Fin n × Fin (a + a')), Rest (evI D.host.F) ⇑g r) ∧
      ∀ g : SInf D.host.F (Fin n × Fin (a + a')), pure g φ = tens (evI D.host.F) ⇑g r :=
    ⟨_, fun g => GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd, fun g => rfl⟩
  have hlist : ∀ (t : ℝ) (L : List (Fin l.length)) (g : SInf D.host.F (Fin n × Fin (a + a'))),
      (L.map fun i => om (1, γ i (Multiplicative.ofAdd t))).prod (tens (evI D.host.F) ⇑g r) =
        tens (evI D.host.F) ⇑((L.map fun i => T i t).prod g) r := by
    intro t L
    induction L with
    | nil => intro g; rfl
    | cons i L ih =>
      intro g
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      rw [ih g]
      exact hTa i t _ r (hR _)
  let κ : GA D X →* UA D.sp.cm.sig Wsp.J :=
    { toFun := kapX X e hJ, map_one' := GlobalTheory.KapXLine.kapX_one X e hJ,
      map_mul' := GlobalTheory.KapXLine.kapX_mul X e hJ }
  let H : GA D X →* Module.End ℂ ((Fin n × Fin (a + a') → AF D.host.F) → ℂ) :=
    (om.comp (MonoidHom.inr _ _)).comp κ
  have hH : ∀ g, H g = om (1, kapX X e hJ g) := fun g => rfl
  have hprod : ∀ t : ℝ, om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) =
      tens (evI D.host.F) ⇑((List.ofFn fun i => T i t).prod f) r := by
    intro t
    rw [← hH, map_list_prod, List.map_map]
    have e1 : l.map (H ∘ fun q => oneP θ X q.1 q.2 t) =
        (List.finRange l.length).map fun i => om (1, γ i (Multiplicative.ofAdd t)) := by
      conv_lhs => rw [← List.ofFn_get l]
      rw [List.map_ofFn, List.ofFn_eq_map]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, hH, hγt]
    rw [e1, hpure, hlist, ← List.ofFn_eq_map]
  have hone : ∀ (i : Fin l.length) (t : ℝ), om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) =
      tens (evI D.host.F) ⇑(T i t f) r := by
    intro i t
    rw [← hγt, hpure]
    exact hTa i t f r (hR f)
  have hd : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j)) * r x) (Ψ i x) 0 := by
    intro i
    have h := (hΨ i).2 x
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show _ = om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) x
    rw [hone]
    rfl
  have hgoal : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) x) =
      fun t => (List.ofFn fun i => T i t).prod f (fun j => evI D.host.F (x j)) * r x := by
    funext t
    rw [hprod]
    rfl
  rw [hgoal]
  by_cases hr : r x = 0
  · have h0 : ∀ i, Ψ i x = 0 := fun i => by
      have := hd i
      simp only [hr, mul_zero] at this
      exact this.unique (hasDerivAt_const _ _)
    simp only [hr, mul_zero, h0, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  · have hc : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j))) (Ψ i x / r x) 0 := fun i => by
      have := (hd i).mul_const (r x)⁻¹
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
      · simp only [mul_assoc, mul_inv_cancel₀ hr, mul_one]
      · rw [div_eq_mul_inv]
    have hcore := _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod hP M Bs.ψ χ₁ χ₂ om hcm hstdB hweil l.length γ hγ T hTa
      hTadd hT0 f (fun j => evI D.host.F (x j)) (fun i => Ψ i x / r x) hc
    refine (hcore.mul_const (r x)).congr_deriv ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ hr

theorem lineSum_exists_derivative_factor_core (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (D : D7) (θ : InfFam D) (X : HSp D)
    {a a' n : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Wsp : Spc D.host.F D.host.E (a + a')) (Vsp : Spc D.host.F D.host.E n)
    (M : Model D.sp.cm.sig Vsp Wsp) (χ₁ χ₂ : (AE D)ˣ →* Circle)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vsp Wsp)
    (hJ : Wsp.J = D.host.xi0 • reindex e e X.gramᵀ) (hθ : IsInfFam θ)
    (hM : M.IsGood Bs.ψ) {p₁ q₁ p₂ q₂ : ℕ}
    (hPair : GlobalTheory.ThK.IsPair Bs M χ₁ χ₂ om p₁ q₁ p₂ q₂)
    (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ) :
    ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Ψ ∈ algD M Bs.ψ Bs.emb,
      ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) ΦD x) (Ψ x) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Wsp hJ
  obtain ⟨Dop, hDP, hD⟩ := (_root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair hP _ _ D.sp.cm.sig Bs _ _ Vsp Wsp M χ₁ χ₂ om _ _ _ _
    hPair).2.2.1 γ hγ
  have hfun : ∀ Φ : (Fin n × Fin (a + a') → AF D.host.F) → ℂ, ∀ x,
      (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) Φ x) = fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x := by
    intro Φ x; funext t; rw [hγt t]
  intro ΦD hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q _ _ hp hq =>
    obtain ⟨p', hp', hdp⟩ := hp
    obtain ⟨q', hq', hdq⟩ := hq
    refine ⟨p' + q', add_mem hp' hq', fun x => ?_⟩
    have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) (p + q) x) =
        fun t => om (1, kapX X e hJ (oneP θ X τ Y t)) p x + om (1, kapX X e hJ (oneP θ X τ Y t)) q x := by
      funext t; simp
    rw [e1]
    exact (hdp x).add (hdq x)
  | smul c p _ hp =>
    obtain ⟨p', hp', hdp⟩ := hp
    refine ⟨c • p', Submodule.smul_mem _ c hp', fun x => ?_⟩
    have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) (c • p) x) =
        fun t => c * om (1, kapX X e hJ (oneP θ X τ Y t)) p x := by
      funext t; simp
    rw [e1]
    simpa using (hdp x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure (Dop f) φ, Submodule.subset_span ⟨Dop f, φ, hDP f hf, hSB, hev, rfl⟩, fun x => ?_⟩
    rw [hfun]
    exact ((hD f hf (Dop f)).2 rfl) _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x

theorem lineSum_product_rule_core (D : D7) (θ : InfFam D) (X : HSp D)
    {a a' n : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Wsp : Spc D.host.F D.host.E (a + a')) (Vsp : Spc D.host.F D.host.E n)
    (M : Model D.sp.cm.sig Vsp Wsp)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vsp Wsp)
    (hJ : Wsp.J = D.host.xi0 • reindex e e X.gramᵀ)
    (l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ))
    (hex : ∀ (Φ : (Fin n × Fin (a + a') → AF D.host.F) → ℂ), Φ ∈ algD M Bs.ψ Bs.emb → ∀ i : Fin l.length,
        ∃ Ψ ∈ algD M Bs.ψ Bs.emb, ∀ x,
        HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) Φ x) (Ψ x) 0)
    (hpure : ∀ f ∈ M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin n × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ Ψ : Fin l.length → (Fin n × Fin (a + a') → AF D.host.F) → ℂ,
        (∀ i, Ψ i ∈ algD M Bs.ψ Bs.emb ∧
            ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) x) (Ψ i x) 0) →
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) x) (∑ i, Ψ i x) 0)
    {ΦD : (Fin n × Fin (a + a') → AF D.host.F) → ℂ} (hΦD : ΦD ∈ algD M Bs.ψ Bs.emb)
    (Ψ : Fin l.length → (Fin n × Fin (a + a') → AF D.host.F) → ℂ)
    (hΨ : ∀ i, Ψ i ∈ algD M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0)
    (x : Fin n × Fin (a + a') → AF D.host.F) :
    HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (∑ i, Ψ i x) 0 := by
  induction hΦD using Submodule.span_induction generalizing Ψ x with
  | zero =>
    have h0 : ∀ i, Ψ i x = 0 := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    simp only [h0, Finset.sum_const_zero]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q hp hq ihp ihq =>
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    choose Ψq hΨq hdq using hex q (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hq)
    have hsplit : ∀ i, Ψ i x = Ψp i x + Ψq i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (p + q) x) =
          fun t => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x +
            om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) q x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).add (hdq i x)
    have e2 : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (p + q) x) =
        fun t => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x +
          om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) q x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).add (ihq Ψq (fun i => ⟨hΨq i, hdq i⟩) x)
  | smul c p hp ihp =>
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    have hsplit : ∀ i, Ψ i x = c * Ψp i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (c • p) x) =
          fun t => c * om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).const_mul c
    have e2 : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (c • p) x) =
        fun t => c * om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    exact hpure f hf φ hSB hev Ψ hΨ x

theorem lineSum_derivative_sum_core (D : D7) (θ : InfFam D) (X : HSp D)
    {a a' n : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Wsp : Spc D.host.F D.host.E (a + a')) (Vsp : Spc D.host.F D.host.E n)
    (M : Model D.sp.cm.sig Vsp Wsp)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vsp Wsp)
    (hJ : Wsp.J = D.host.xi0 • reindex e e X.gramᵀ)
    (l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ))
    {ΦD : (Fin n × Fin (a + a') → AF D.host.F) → ℂ} {Φ₁D : (Fin n × Fin (a + a') → AF D.host.F) → ℂ}
    (hex : ∀ i : Fin l.length, ∃ Ψ ∈ algD M Bs.ψ Bs.emb, ∀ x,
        HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ x) 0)
    (hpr : ∀ Ψ : Fin l.length → (Fin n × Fin (a + a') → AF D.host.F) → ℂ,
        (∀ i, Ψ i ∈ algD M Bs.ψ Bs.emb ∧
          ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) →
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (∑ i, Ψ i x) 0)
    (hΦ₁ : ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) :
    ∃ Ψ : Fin l.length → (Fin n × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  choose Ψ hΨ hder using hex
  refine ⟨Ψ, fun i => ⟨hΨ i, hder i⟩, ?_⟩
  funext x
  rw [Finset.sum_apply]
  exact (hΦ₁ x).unique (hpr Ψ (fun i => ⟨hΨ i, hder i⟩) x)

theorem conjugateUnitaryAdelicIso_map_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem algebraicDatum_eq_sum_pureTensors_vacua {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  rw [algD, Submodule.mem_span_set'] at hΦ
  obtain ⟨m, c, g, rfl⟩ := hΦ
  choose f φ hf hφ hv hg using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem lineDerivation_isDerivation_of_datum_core (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs)
    (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W₀ X : HSp D)
    {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Wsp : Spc D.host.F D.host.E (a + a')) (Vsp : Spc D.host.F D.host.E W₀.rank)
    (M : Model D.sp.cm.sig Vsp Wsp) (χ₁ χ₂ : (AE D)ˣ →* Circle)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vsp Wsp)
    (ω₀ : WRep W₀ X) (c₀ : Matrix (Fin W₀.rank) (Fin (a + a')) (AE D) ≃+ WO W₀ X)
    (hJX : Wsp.J = D.host.xi0 • reindex e e X.gramᵀ) (cJ : D.host.E) (hJV : Vsp.J = cJ • W₀.gram)
    (hθ : IsInfFam θ) (hpsi : Bs.ψ = ψ) (hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hstdB : IsStd Bs.ψ) (hM : M.IsGood Bs.ψ) (hweil : M.IsWeil Bs.ψ χ₁ χ₂ om)
    (hderPol : ∀ γ ∈ Lines D.sp.cm.sig Wsp, ∃ δ : SInf D.host.F (Fin W₀.rank × Fin (a + a')) →ₗ[ℂ] SInf D.host.F (Fin W₀.rank × Fin (a + a')),
        ∀ f ∈ M.Pol Bs.ψ Bs.emb, δ f ∈ M.Pol Bs.ψ Bs.emb ∧
          ActsD (evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f))
    (hweil0 : ∀ ΦD Φ, IsDatum M ψ c₀ ΦD Φ → ∀ g h,
        IsDatum M ψ c₀ (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₀ cJ hJV g, kapX X e hJX h) ΦD) (ω₀ (g, h) Φ))
    (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ)
    (ΦD : (Fin W₀.rank × Fin (a + a') → AF D.host.F) → ℂ) (hΦD : ΦD ∈ algD M Bs.ψ Bs.emb)
    (Ψ : (Fin W₀.rank × Fin (a + a') → AF D.host.F) → ℂ)
    (hD : ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0)
    (Φ Φ' : WO W₀ X → ℂ) (hDat : IsDatum M ψ c₀ ΦD Φ) (hDat' : IsDatum M ψ c₀ Ψ Φ') :
    IsDer θ X (fun h => ω₀ (1, h)) τ Y Φ Φ' := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Wsp hJX
  obtain ⟨δ, hδ⟩ := hderPol γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := algebraicDatum_eq_sum_pureTensors_vacua M Bs.ψ Bs.emb hΦD
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 :=
    fun i => ((hf i).2.2.and hM.std).mono fun v h => h.1.trans h.2
  have hder : ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x)
      ((∑ i, pure (δ (f i)) (φ i)) x) 0 := by
    intro x
    have e1 : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x) =
        fun t => ∑ i, om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x := by
      funext t
      rw [map_sum, Finset.sum_apply]
    rw [e1, Finset.sum_apply]
    exact HasDerivAt.fun_sum fun i _ =>
      (hδ _ (hf i).1).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hΨe : Ψ = ∑ i, pure (δ (f i)) (φ i) := by
    funext x
    have h1 := hD x
    simp only [← hγt] at h1
    exact h1.unique (hder x)
  intro z
  obtain ⟨u, rfl⟩ := c₀.surjective z
  have hs : IsStd ψ := hpsi ▸ hstdB
  have hg : M.IsGood ψ := hpsi ▸ hM
  have hw : M.IsWeil ψ χ₁ χ₂ om := hpsi ▸ hweil
  have key := _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line hP M ψ χ₁ χ₂ om hcm hs hg hw γ hγ m f (fun i => δ (f i)) φ
    (fun i => (hf i).2) (fun i => (hδ _ (hf i).1).2) u
  have e2 : (fun t : ℝ => ω₀ (1, oneP θ X τ Y t) Φ (c₀ u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)))) := by
    funext t
    have h1 := (hweil0 _ Φ hDat 1 (oneP θ X τ Y t)).2 u
    rw [conjugateUnitaryAdelicIso_map_one, ← hγt t] at h1
    exact h1.symm
  rw [e2, ← hDat'.2 u, hΨe]
  exact key

theorem ker_projection_eq_line_weyl_core (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (W₀ X : HSp D) (A₀ : Fr W₀) (B : Fr X) (b : Bool) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Wsp : Spc D.host.F D.host.E (a + a')) (Vsp : Spc D.host.F D.host.E W₀.rank)
    (M : Model D.sp.cm.sig Vsp Wsp)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vsp Wsp)
    (ω₀ : WRep W₀ X) (c₀ : Matrix (Fin W₀.rank) (Fin (a + a')) (AE D) ≃+ WO W₀ X)
    (hJX : Wsp.J = D.host.xi0 • reindex e e X.gramᵀ) (hθ : IsInfFam θ) (hψ : IsStd ψ)
    (halg : ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ b A₀ B, IsDatum M ψ c₀ ΦD Φ)
    (hsumDer : ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
        ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ Φ₁D : (Fin W₀.rank × Fin (a + a') → AF D.host.F) → ℂ,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJX ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
        ∃ Ψ : Fin l.length → (Fin W₀.rank × Fin (a + a') → AF D.host.F) → ℂ,
          (∀ i, Ψ i ∈ algD M Bs.ψ Bs.emb ∧
            ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJX (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
          Φ₁D = ∑ i, Ψ i)
    (hlinDer : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ Ψ ∈ algD M Bs.ψ Bs.emb,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
        IsDatum M ψ c₀ ΦD Φ → IsDatum M ψ c₀ Ψ Φ' → IsDer θ X (fun h => ω₀ (1, h)) τ Y Φ Φ')
    {M' : Type*} [AddCommGroup M'] [Module ℂ M'] (L_act : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → M' →ₗ[ℂ] M')
    (p₁ : (WO W₀ X → ℂ) →ₗ[ℂ] M')
    (heql' : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ b A₀ B, ∀ Φ' ∈ algF ψ θ b A₀ B,
        IsDer θ X (fun h => ω₀ (1, h)) τ Y Φ Φ' → p₁ Φ' = L_act τ Y (p₁ Φ))
    (γ : Multiplicative ℝ →* UA D.sp.cm.sig Wsp.J) (hγ : γ ∈ Lines D.sp.cm.sig Wsp)
    (ΦD : (Fin W₀.rank × Fin (a + a') → AF D.host.F) → ℂ) (hΦD : ΦD ∈ algD M Bs.ψ Bs.emb)
    (Φ₁D : (Fin W₀.rank × Fin (a + a') → AF D.host.F) → ℂ)
    (hder : ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) ΦD x) (Φ₁D x) 0)
    (Φ Φ₁ : WO W₀ X → ℂ) (hD : IsDatum M ψ c₀ ΦD Φ) (hD₁ : IsDatum M ψ c₀ Φ₁D Φ₁) (hp : p₁ Φ = 0) :
    p₁ Φ₁ = 0 := by
  obtain ⟨l, hl, hγl⟩ := GlobalTheory.T.oneParamSubgroup_transposeGramUnitary_decomposes D θ X e Wsp hJX hθ γ hγ
  have hder' : ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJX ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x)
      (Φ₁D x) 0 := by
    intro x; have := hder x; simp only [hγl] at this; exact this
  obtain ⟨Ψ, hΨ, hsum⟩ := hsumDer l hl ΦD hΦD Φ₁D hder'
  have hΦF : Φ ∈ algF ψ θ b A₀ B := by
    obtain ⟨Φ', hΦ', hD'⟩ := halg ΦD hΦD
    rwa [IsDatum.fun_eq M ψ c₀ c₀.surjective hD hD']
  choose Φ' hΦ'F hΦ'D using fun i => halg (Ψ i) (hΨ i).1
  have hsumD : ∀ s : Finset (Fin l.length), IsDatum M ψ c₀ (∑ i ∈ s, Ψ i) (∑ i ∈ s, Φ' i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (CoinvPass.isDatum_zero (M := M) (ψ := ψ) (crd := c₀))
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact CoinvPass.isDatum_add hψ (hΦ'D a) ih
  have hΦ₁ : Φ₁ = ∑ i, Φ' i := IsDatum.fun_eq M ψ c₀ c₀.surjective hD₁ (hsum ▸ hsumD Finset.univ)
  rw [hΦ₁, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := hl _ (List.get_mem l i)
  rw [heql' _ _ hi Φ hΦF (Φ' i) (hΦ'F i)
    (hlinDer _ _ hi ΦD hΦD (Ψ i) (hΨ i).1 (hΨ i).2 Φ (Φ' i) hD (hΦ'D i)), hp, map_zero]

end GlobalTheory.LineDerivCore

namespace GlobalTheory.PureProdRule
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
    ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0 :=
  fun hP D θ X _ _ e Bs Γ Xc om _ hJ hθ hTr l hl f hf φ hφ hvac Ψ hΨ x =>
    GlobalTheory.LineDerivCore.lift_splits_locally_core hP D θ X e Bs Γ.W Γ.V Γ.M Xc.β (Xc.β / Xc.α) om hJ hθ hTr.base.cm hTr.base.std hTr.geo.hM hTr.weil l hl f hf φ hφ hvac Ψ hΨ x
end GlobalTheory.PureProdRule

namespace GlobalTheory.LineSum
theorem lineSum_exists_derivative_factor (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hθ : IsInfFam θ) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ) :
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∃ Ψ ∈ algD Γ.M Bs.ψ Bs.emb,
      ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) ΦD x) (Ψ x) 0 :=
  GlobalTheory.LineDerivCore.lineSum_exists_derivative_factor_core hP D θ X e Bs Γ.W Γ.V Γ.M Xc.β (Xc.β / Xc.α) om hJ hθ hT.geo.hM (GlobalTheory.ThK.RealUniq.isPair_V hT) τ Y hY

theorem lineSum_product_rule (hpure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
    ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (∑ i, Ψ i x) 0 :=
  fun hP D θ X _ _ e Bs Γ Xc om om' hJ hθ hT l hl _ hΦD Ψ hΨ x =>
    GlobalTheory.LineDerivCore.lineSum_product_rule_core D θ X e Bs Γ.W Γ.V Γ.M om hJ l
      (fun Φ hΦ i => lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) Φ hΦ)
      (hpure hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl) hΦD Ψ hΨ x

theorem lineSum_derivative_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i :=
  fun hP D θ X _ _ e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD _ hΦ₁ =>
    GlobalTheory.LineDerivCore.lineSum_derivative_sum_core D θ X e Bs Γ.W Γ.V Γ.M om hJ l
      (fun i => lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) ΦD hΦD)
      (lineSum_product_rule _root_.GlobalTheory.PureProdRule.lift_splits_locally hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD)
      hΦ₁
end GlobalTheory.LineSum

namespace GlobalTheory.SquareAgree.LineDerFun

theorem lineDerivation_isDerivation_of_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Ψ ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hO.JX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Ψ Φ' → IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' :=
  fun hP D ψ θ W _ X _ _ _ _ _ _ _ _ _ ωA _ e Bs Γ Xc om om' cA _ hθ _ hO hT τ Y hY ΦD hΦD Ψ _ hD Φ Φ' hDat hDat' =>
    GlobalTheory.LineDerivCore.lineDerivation_isDerivation_of_datum_core hP D ψ θ W X e Bs Γ.W Γ.V Γ.M Xc.β (Xc.β / Xc.α) om ωA cA
      hO.JX 1 hO.JW hθ hO.psi hT.base.cm hT.base.std hT.geo.hM hT.weil
      (fun γ hγ => GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw Bs Γ Xc om om' hT γ hγ)
      hO.weilA τ Y hY ΦD hΦD Ψ hD Φ Φ' hDat hDat'

end GlobalTheory.SquareAgree.LineDerFun

namespace GlobalTheory.LineKerW
theorem ker_projection_eq_line_weyl : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) ΦD x) (Φ₁D x) 0) → ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ = 0 → p Φ₁ = 0 :=
  fun hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' Pi rf rl p p' hm γ hγ ΦD hΦD Φ₁D _ hder Φ Φ₁ hD hD₁ hp =>
    GlobalTheory.LineDerivCore.ker_projection_eq_line_weyl_core D ψ θ W X A B true e Bs Γ.W Γ.V Γ.M om ωA cA
      hO.JX hθ (hO.psi ▸ hT'.base.std) hO.algA'
      (_root_.GlobalTheory.LineSum.lineSum_derivative_sum hP D θ X e Bs Γ Xc om om' hO.JX hθ hT')
      (_root_.GlobalTheory.SquareAgree.LineDerFun.lineDerivation_isDerivation_of_datum hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT')
      rl p hm.mapA.eql
      γ hγ ΦD hΦD Φ₁D hder Φ Φ₁ hD hD₁ hp
end GlobalTheory.LineKerW

end
