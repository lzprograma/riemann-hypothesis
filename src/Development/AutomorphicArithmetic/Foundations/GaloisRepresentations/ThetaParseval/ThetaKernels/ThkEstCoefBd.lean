module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowModel
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefReal
public import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInj
public import Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
public import Development.WeilBound.ThetaLifts.FrameEstimates.LevelA
public import Development.WeilBound.ThetaLifts.FrameEstimates.Parity
public import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsCharNe
public import Development.WeilBound.ThetaLifts.FrameEstimates.LatCpt
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsD
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear

/-! # ThkEstCoefBd: Consolidated global theta-kernel definitions and proofs (ThkEstCoefBd). -/
@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open scoped TensorProduct NNReal Matrix
open GlobalTheory.ThK (IsPair_k)

noncomputable section

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace PositivityTheory.ThKEst
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
def Level_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s',
    IsPair_k B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ W.J),
    ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (1,
    u) (pureA F f φ) = pureA F f φ
end PositivityTheory.ThKEst
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKEnd.Grp
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
theorem level_sch_k (hL : PositivityTheory.ThKEst.Level_k) {n : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E}
  {M : Model σ X W} {χX χW om r s r' s'}
    (hp : IsPair_k B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    ∀ᶠ u in 𝓝 (1 : UA σ W.J), (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (1, u) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨U, hU, h⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp g hg
    exact mem_of_superset hU fun u hu k => h u hu k f
  | zero => exact Eventually.of_forall fun _ _ => map_zero _
  | add x y _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add (f := _), h1 k, h2 k]
  | smul a x _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]
end PositivityTheory.ThKEnd.Grp
end
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
namespace PositivityTheory.ThKF
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
def ArchOp_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
      IsPair_k B M χX χW om r s r' s' →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∃ T, IsArchOp om (g, h) T ∧
      (g ∈ KInf σ X B.emb → h ∈ KInf σ W B.emb → ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb)
end PositivityTheory.ThKF
end

section
namespace GlobalTheory.ThK.Dbl.Prs
open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)
variable {a a' n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W} {o : Rep σ Y W} {R : RealMaps
  F a a'} {Rf : FinMaps F a a'} {p : SInf F (Fin n × Fin d) →ₗ[ℂ] R.Pi} {q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ]
  Rf.Pi v} {T T₁ : Finset (Pl F)}
theorem inf_op_k (hA : PositivityTheory.ThKF.ArchOp_k) {χ χ' r s r' s'} (hp : IsPair_k B
  M χ χ' o r s r' s') {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ A : Module.End ℂ (SInf F (Fin n × Fin d)), ∀ f ∈ M.Pol B.ψ B.emb, A f ∈ M.Pol B.ψ B.emb ∧ Acts (evI F) (o (1,
      k)) f (A f) := by
  have o1 : (1 : UA σ Y.J) ∈ KInf σ Y B.emb :=
    ⟨fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero], fun w => by
      rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp 1 o1.1 k hk.1
  exact ⟨A, fun f hf => ⟨a2 o1 hk f hf, a1.2 f⟩⟩
end GlobalTheory.ThK.Dbl.Prs
end
end

section
namespace PositivityTheory.ThKEst
section
open scoped TensorProduct ENNReal NNReal Classical
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.ThK NumberField.mixedEmbedding W
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
theorem coefBd_of_k : CoefReal → CoefBd_k := by
  intro hR F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ φ₁ h₁ φ₂ h₂ N
  have := hP.base.cm.1
  obtain ⟨p, C, K, hp, hC, hK, h⟩ := coef_split hR hP.base.std μ hμ h₁ h₂ N
  obtain ⟨L, hL, hsz⟩ := sz_le B.emb M.co.e.symm.toLinearMap
  have hLN : 0 ≤ C * L ^ N := by positivity
  refine ⟨(NNReal.mk (1 + C * L ^ N) (by positivity)) • p,
    (fun q => M.co.e.symm (spl F _ (0, q.1), spl F _ (0, q.2))) '' K, hp.const_smul _,
    hK.image ((lin_cont M.co.e.symm.toLinearMap).comp ((spl_cont.comp (continuous_const.prodMk continuous_fst)).prodMk
      (spl_cont.comp (continuous_const.prodMk continuous_snd)))), fun f₁ f₂ z => ?_⟩
  obtain ⟨w, rfl⟩ := M.co.e.symm.surjective z
  obtain ⟨x, hx⟩ := (spl F _).surjective w.1
  obtain ⟨y, hy⟩ := (spl F _).surjective w.2
  obtain rfl : w = (spl F _ x, spl F _ y) := Prod.ext hx.symm hy.symm
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨a, b⟩ := h f₁ f₂ x y
  by_cases h0 : coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (spl F _ x, spl F _ y) = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (LatticeQuotientCompactness.maj_nonneg _ _ _ _)
  have s0 := LatticeQuotientCompactness.sz_nonneg B.emb (M.co.e.symm (spl F _ x, spl F _ y))
  rw [maj, ite_eq_left, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  · have q := mul_nonneg (apply_nonneg p f₁) (apply_nonneg p f₂)
    calc _ ≤ _ * (L * (1 + ‖x.1‖ + ‖y.1‖)) ^ N := by gcongr; exact hsz x y
      _ = L ^ N * (_ * (1 + ‖x.1‖ + ‖y.1‖) ^ N) := by rw [mul_pow, mul_left_comm]
      _ ≤ L ^ N * (C * (p f₁ * p f₂)) := by gcongr
      _ ≤ ((1 + C * L ^ N) * p f₁) * ((1 + C * L ^ N) * p f₂) := by
        nlinarith [mul_nonneg hLN q, mul_nonneg (mul_nonneg hLN hLN) q]
  · refine ⟨_, ⟨_, b h0, rfl⟩, fun u hu => ?_⟩
    rw [← map_sub, ← map_smul, map_eq_zero_iff _ M.co.e.symm.injective, Prod.mk_sub_mk, ← map_sub, ← map_sub]
    have : ∀ x : (Fin n × Fin d → mixedSpace F) × (Fin n × Fin d → Af F), u • spl F _ (x - (0, x.2)) = 0 := fun x =>
      funext fun i => by
        show u * (re F _ + fi F (x.2 i - x.2 i)) = 0
        rw [sub_self, map_zero, add_zero, ← re_add_fi u, hu, map_zero, zero_add, mul_comm, re_mul_fi]
    exact Prod.ext (this x) (this y)
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
theorem coefEq_of_k : CoefEq_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ Φ₁ h₁ Φ₂ h₂ g h z
  have hs := IsUWeilPair.isUSplitting hP.weil
  set w := mat g⁻¹ * z * (mat h⁻¹)ᵀ with hw
  have e : actAB (cA σ) (g, h) w = z := by
    have a : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1
    have b : (mat h⁻¹)ᵀ * (mat h)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show mat h * mat h⁻¹ = 1 from Units.mul_inv h.1, Matrix.transpose_one]
    change mat g * w * (mat h)ᵀ = z
    rw [hw, Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g), a, Matrix.one_mul, Matrix.mul_assoc, b,
      Matrix.mul_one]
  have i := hs.impl (g, h) w Φ₁ h₁
  rw [e] at i
  have k := inner_eq_of_unit μ (om (g, h)) (hs.pres _) (hs.unit μ hμ _)
    (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std w Φ₁ h₁) h₂
  rw [i] at k
  exact k
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open levelStructure in
theorem level_of_k (hC : CoefEq_k) (hF : FourierInj) (hB : CoefBd_k) : Level_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := coef_near M hp.base.std hφ hCc
  have := LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ W.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtypeVal).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, one_apply_eq_self, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1,
    u) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv,
      Matrix.one_mul]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)
    · unfold coef
      rw [← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1,
        Matrix.transpose_one, Matrix.mul_one]
    have b := hb f f₀ z
    have b' := hb f f₀ (z * (mat u⁻¹)ᵀ)
    rw [maj, ite_eq_right a, mul_zero, norm_le_zero_iff] at b
    rw [maj, ite_eq_right a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul,
        mul_apply_eq_comp, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near c fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem level_k : Level_k := level_of_k coefEq_of_k fourierInj_of (coefBd_of_k coefReal_of)
end
end PositivityTheory.ThKEst
end

section
namespace PositivityTheory.ThKF.A
open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real
  RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKF.W
  GlobalTheory.HeisSchA GlobalTheory.RealWeil
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X :
  Spc F E n} {W : Spc F E d}
variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
theorem impl_of_k (hP : IsPair_k B M χX χW om r s r' s') (C : Coord F (Fin n × Fin d)) {x}
    {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (h : ∀ f : SInf F _, ∀ g ∈ SB (Fin n × Fin d → Af F), om x (pureA F f g) = pureA F (T f) g) :
    PositivityTheory.ThKF.E.Impl (C.P ≪≫ₗ phL M x ≪≫ₗ C.P.symm) (C.S.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ
      C.S.symm.toLinearEquiv.toLinearMap) := by
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  refine ⟨fun f => ?_, fun w f g hg => ?_⟩
  · obtain ⟨f, rfl⟩ := C.S.surjective f
    have := C.norm_eq (lintegral_eq (fun μ hμ => hs.unit μ hμ x) (h f))
    simpa using this
  · obtain ⟨f, rfl⟩ := C.S.surjective f
    obtain ⟨g, rfl⟩ := C.S.surjective g
    rw [C.rho_iff hP.base.std] at hg
    have : ⇑(T g) = schrInf F B.ψ (C.P (C.P.symm (phL M x (C.P w)))) (T f) := by
      refine pureA_inj h₁ ?_
      rw [← h g _ h₀, hg, pureA_schrInf, pureA_schrInf, ← h f _ h₀, LinearEquiv.apply_symm_apply, ← phL_spec]
      obtain ⟨u, hu⟩ := M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))
      rw [← hu, phB_e]
      exact hs.impl x u _ (pureA_mem f h₀)
    simpa using (C.rho_iff hP.base.std _ _ _).2 this
theorem exists_T_k (hP : IsPair_k B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh :
  h ∈ UAt σ W (evI F)) :
    ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ := by
  have hs := IsUWeilPair.isUSplitting hP.weil
  refine exists_lin hP.base.std _ (hs.pres _) fun m Φ hΦ => ?_
  obtain ⟨u, hu⟩ := M.co.e.surjective (finE2 F m)
  have := hs.impl (g, h) u Φ hΦ
  simp only [Darboux.rho] at this
  rw [← phB_e, hu, phB_fin M hg hh] at this
  exact this
theorem surj_of_k (hP : IsPair_k B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh :
  h ∈ UAt σ W (evI F))
    {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ) :
    Function.Surjective T := fun f => by
  obtain ⟨T', hT'⟩ := exists_T_k hP (inv_mem_UAt hg) (inv_mem_UAt hh)
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  refine ⟨T' f, DFunLike.coe_injective (pureA_inj h₁ ?_)⟩
  rw [← hT _ _ h₀, ← hT' _ _ h₀, ← mul_apply_eq_comp, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel]
  exact LinearMap.congr_fun om.map_one _
theorem T_D_k (hP : IsPair_k B M χX χW om r s r' s') (C : Coord F (Fin n × Fin d)) {g h} (hg : g
  ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ) (v) (f) :
    T (C.D v f) = C.D (phL M (g, h) v) (T f) := by
  have := PositivityTheory.ThKF.E.Impl.dRho (s := (C.P ≪≫ₗ phL M (g, h) ≪≫ₗ C.P.symm).toLinearMap) (impl_of_k hP C hT)
    (C.S.surjective.comp ((surj_of_k hP hg hh hT).comp C.S.symm.surjective)) (C.P.symm v) (C.S f)
  apply C.S.injective
  simpa [Coord.D] using this
theorem exists_op_k (hP : IsPair_k B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh
  : h ∈ UAt σ W (evI F)) :
    ∃ T, IsArchOp om (g, h) T := by
  obtain ⟨T, hT⟩ := exists_T_k hP hg hh
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hc := (impl_of_k hP C hT).continuous (C.S.surjective.comp ((surj_of_k hP hg hh hT).comp C.S.symm.surjective))
  have hc' : Continuous T := by
    have := C.S.symm.continuous.comp (hc.comp C.S.continuous)
    convert this using 1
    funext f
    simp
  exact ⟨⟨T, hc'⟩, hT, acts_of hT⟩
theorem map_Pol_k (hP : IsPair_k B M χX χW om r s r' s') {X₂ : Spc F E n} {W₂ : Spc F E d} (M₂ :
  Model σ (reS X X₂) (reS W W₂))
    (hco : M₂.co = M.co) {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F))
    (eg : ∀ w, (mat g).map (piInf (B.emb w)) * X₂.θ w = X.θ w * (mat g).map (piInf (B.emb w)))
    (eh : ∀ w, (mat h).map (piInf (B.emb w)) * W₂.θ w = W.θ w * (mat h).map (piInf (B.emb w)))
    {T} (hT : IsArchOp om (g, h) T) : ∀ f ∈ M₂.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb := by
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hψ := hP.base.std
  have hl : ∀ u, M₂.heisLine B.ψ u = M.heisLine B.ψ u := fun u => funext fun t => by
    unfold Model.heisLine
    rw [hco]
    rfl
  have uq := fun f f₁ f₂ => (archUniq F (Fin n × Fin d) f f₁ f₂).2
  have hD := T_D_k hP C hg hh (T := T.toLinearMap) hT.1
  intro f hf
  refine Submodule.mem_sInf.1 hf ((M.Pol B.ψ B.emb).comap T.toLinearMap) ⟨fun f₀ ⟨ε, hε⟩ => ?_,
    fun u hu f hf f₁ h₁ => ?_⟩
  · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ⟨ε, fun u u' hu hu' e f f' h1 h2 => ?_⟩
    have k : ∀ z, actAB (cA σ) (g, h) (actAB (cA σ) (g⁻¹, h⁻¹) z) = z := fun z => (actLin (R := AF F) (cA σ) (g,
      h)).right_inv z
    have a1 := at_act (g⁻¹, h⁻¹) hu
    have a2 := at_act (g⁻¹, h⁻¹) hu'
    have hA : ∀ z, At (evI F) z → ActsD (evI F) (M₂.heisLine B.ψ z) f₀ (C.D (vec M z) f₀) := fun z hz => by
      rw [hl]
      exact actsD_heis hψ M C hz f₀
    have hD' : ∀ z, At (evI F) z → C.D (vec M (actAB (cA σ) (g, h) z)) (T f₀) = T (C.D (vec M z) f₀) := fun z hz => by
      rw [← phL_vec M _ hz]
      exact (hD _ _).symm
    have b1 := hD' _ a1
    have b2 := hD' _ a2
    rw [k] at b1 b2
    have key := hε _ _ a1 a2 (fun w => ?_) _ _ (hA _ a1) (hA _ a2)
    · have c1 : f = C.D (vec M u) (T f₀) := uq _ _ _ _ h1 (actsD_heis hψ M C hu (T f₀))
      have c2 : f' = C.D (vec M u') (T f₀) := uq _ _ _ _ h2 (actsD_heis hψ M C hu' (T f₀))
      rw [c1, c2, b1, b2, key, map_smul]
    · have inv : ∀ {m : ℕ} (a b θ θ' : Matrix (Fin m) (Fin m) ℂ), b * a = 1 → a * θ' = θ * a → b * θ = θ' * b :=
        fun a b θ θ' h1 h2 => by
          have h3 := mul_eq_one_comm.1 h1
          calc b * θ = b * (θ * a) * b := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
            _ = θ' * b := by rw [← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have i1 := inv _ ((mat g⁻¹).map (piInf (B.emb w))) _ _ (by
        rw [← Matrix.map_mul, show mat g⁻¹ * mat g = 1 from Units.inv_mul g.1,
          Matrix.map_one _ (map_zero _) (map_one _)]) (eg w)
      have i2 := inv _ ((mat h⁻¹).map (piInf (B.emb w))) _ _ (by
        rw [← Matrix.map_mul, show mat h⁻¹ * mat h = 1 from Units.inv_mul h.1,
          Matrix.map_one _ (map_zero _) (map_one _)]) (eh w)
      have i3 := congrArg Matrix.transpose i2
      rw [Matrix.transpose_mul, Matrix.transpose_mul] at i3
      show (mat g⁻¹ * u' * (mat h⁻¹)ᵀ).map _ = _ • (X₂.θ w * (mat g⁻¹ * u * (mat h⁻¹)ᵀ).map _ * (W₂.θ w)ᵀ)
      simp only [Matrix.map_mul, e w, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simp only [← Matrix.mul_assoc, i1]
      simp only [Matrix.mul_assoc, i3]
  · rw [hl] at h₁
    rw [uq _ _ _ _ h₁ (actsD_heis hψ M C hu _), Submodule.mem_comap, hD]
    exact D_mem_Pol hψ M C _ _ hf
theorem archOp_k : ArchOp_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP g hg h hh
  obtain ⟨T, hT⟩ := exists_op_k hP hg hh
  exact ⟨T, hT,
    fun kg kh => map_Pol_k hP (X₂ := X) (W₂ := W) M rfl hg hh (fun w => (kg.2 w).eq) (fun w => (kh.2 w).eq) hT⟩
end PositivityTheory.ThKF.A
end
end
