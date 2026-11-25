module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftConvergence
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LinearFormAdelic
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.ContinuousFrameUM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InclRSmul
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Std.Tactic.BVDecide.Normalize.Prop

/-! # ArchimedeanChartGaussianInvariant: Consolidated global theta-kernel definitions and proofs (ArchimedeanChartGaussianInvariant). -/
@[expose] public section

open UpperTheory.TP.W (GoodK)
open scoped NNReal Classical ComplexOrder
open scoped ENNReal
open GlobalTheory.Doubling (absE)

noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Algebra.TensorProduct (map map_tmul)

section
namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas
open Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem sigma_invol'_k {B : Base F E} (hB : GoodK σ B) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem exists_ne_sigma_k {B : Base F E} (hB : GoodK σ B) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push Not at hne
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hB.cm.2.1.isComplex _
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  show NumberField.ComplexEmbedding.conjugate τ = τ
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  show star (τ x) = τ x
  rw [← hB.cm.2.2.2 τ x, hne x]
theorem fixed_mem_k {B : Base F E} (hB : GoodK σ B) {q : E} (hq : σ q = q) : ∃ f : F,
  algebraMap F E f = q := by
  by_contra hne
  push Not at hne
  have hli : LinearIndependent F ![(1 : E), q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    · exfalso
      apply hne (-(s / t))
      have h1 := eq_neg_of_add_eq_zero_right hst
      have h2 : q = t⁻¹ • -(s • (1 : E)) := by rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [hB.cm.2.2.1]; rfl
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hσid : σ.toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    fin_cases i
    · simp
    · simpa using hq
  obtain ⟨x, hx⟩ := exists_ne_sigma_k hB
  exact hx (by simpa using LinearMap.congr_fun hσid x)
theorem eig_line_k {B : Base F E} (hB : GoodK σ B) {k : ℤ} (hk : k * k = 1) {δ y : E} (hδ0 : δ ≠
  0)
    (hδ : σ δ = (k : E) * δ) (hy : σ y = (k : E) * y) : ∃ f : F, y = f • δ := by
  have hk0 : (k : E) ≠ 0 := by
    intro h
    have h1 : ((k * k : ℤ) : E) = 1 := by rw [hk]; simp
    rw [Int.cast_mul, h, zero_mul] at h1
    exact zero_ne_one h1
  have hfix : σ (y / δ) = y / δ := by
    rw [map_div₀, hy, hδ, mul_div_mul_left _ _ hk0]
  obtain ⟨f, hf⟩ := fixed_mem_k hB hfix
  refine ⟨f, ?_⟩
  rw [Algebra.smul_def, hf, div_mul_cancel₀ _ hδ0]
theorem eig_AE_k {B : Base F E} (hB : GoodK σ B) {k : ℤ} (hk : k * k = 1) {δ : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = (k : E) * δ) {z : AE F E} (hz : cA σ z = (k : AE F E) * z) :
    z = linearFormAdelic δ z • inclR (AF F) δ := by
  have hinv := sigma_invol'_k hB
  set ℓ : E →ₗ[F] F := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef
  have hℓ : ℓ δ = 1 := ell_spec hδ0
  have hsm : ∀ x : E, (k : F) • x = (k : E) * x := fun x => by rw [Algebra.smul_def, map_intCast]
  have hkk : (k : F) * k = 1 := by exact_mod_cast hk
  let g := ℓ.smulRight δ
  let p := LinearMap.id + (k : F) • σ.toLinearMap
  have hzero : (LinearMap.id - g) ∘ₗ p = 0 := by
    ext e
    have hw : σ (e + (k : F) • σ e) = (k : E) * (e + (k : F) • σ e) := by
      rw [hsm (σ e), map_add (f := _), map_mul, map_intCast, hinv, mul_add, ← mul_assoc, ← Int.cast_mul, hk,
        Int.cast_one, one_mul,
        add_comm]
    obtain ⟨f, hf⟩ := eig_line_k hB hk hδ0 hδ hw
    show (e + (k : F) • σ e) - ℓ (e + (k : F) • σ e) • δ = 0
    rw [hf, map_smul, hℓ, smul_eq_mul, mul_one, sub_self]
  have hbc : ∀ w : AE F E, (LinearMap.id - g).baseChange (AF F) w = w - linearFormAdelic δ w • inclR (F :=
    F) (AF F) δ := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [LinearMap.baseChange_tmul, inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [linearFormAdelic, g, LinearMap.baseChange_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul]
      rfl
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, map_add (f := _), add_smul]
      abel
  have hpc : ∀ w : AE F E, p.baseChange (AF F) w = w + (k : F) • cA σ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      simp [p, cA, LinearMap.baseChange_tmul]
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, map_add (f := _), smul_add]
      abel
  have hkz : (k : F) • cA σ z = z := by
    rw [hz, show ((k : ℤ) : AE F E) = algebraMap F (AE F E) (k : F) by rw [map_intCast], ← Algebra.smul_def, smul_smul,
      hkk,
      one_smul]
  have h2 : p.baseChange (AF F) z = (2 : F) • z := by
    rw [hpc, hkz, two_smul]
  have h0 : (LinearMap.id - g).baseChange (AF F) (p.baseChange (AF F) z) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hzero, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [h2, LinearMap.map_smul_of_tower, hbc] at h0
  exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left two_ne_zero))
end PositivityTheory.SiegelWeilFormula.Act.C5.Meas
end

section
open scoped BoundedContinuousFunction ContDiff
open Formalism.IndefR.DatumF Matrix GlobalTheory.RealWeil GlobalTheory.RealWeilF Classical
open GlobalTheory.ThetaOfSmF in
theorem GlobalTheory.ThetaOfSmF.theta_of_smF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix
      (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι hι hψ f hF hl
  refine ⟨f.2, hl, f.1.continuous, fun k L hL hL0 w => ?_⟩
  obtain ⟨lam, hlc, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log
    (GlobalTheory.T.standard_additive_character_sign F E σ B hB)
  let P : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) :=
    { toFun := fun t => piWF θ (L t)
      map_zero' := by
        funext p
        simp only [piWF, map_zero, Matrix.zero_apply, Pi.zero_apply]
      map_add' := fun s t => by
        funext p
        simp only [piWF, map_add (f := _), Matrix.add_apply, Pi.add_apply] }
  have hP : Continuous P := continuous_pi fun p =>
    (continuous_theta_infPartF (hθ p.2)).comp ((continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hL))
  have hLP : ∀ t, L t = iotaVF ι (P t) := by
    intro t
    ext i j
    refine sub_eq_zero.1 (hι.ext _ ?_ fun w' => ?_)
    · have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hL0 t) i) j
      rw [map_sub, h0]
      simp only [iotaVF, Matrix.of_apply, hι.fin, sub_zero]
    · rw [map_sub, map_sub]
      simp only [iotaVF, Matrix.of_apply, hι.comp]
      show θ w' (infPartF F E (L t i j)) - θ w' (infPartF F E (L t i j)) = 0
      exact sub_self _
  let φ : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun t => -lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero, neg_zero]
      map_add' := fun s t => by
        rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _), neg_add] }
  have hφ := (hlc.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)).neg
  have e : (fun t => f.1 (w + L t)) =
      fun t => Complex.exp (φ.toRealLinearMap hφ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P.toRealLinearMap hP t) f) :=
        by
    funext t
    have h1 : (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f).1 w = heisOF σ JS JT ξ₀ B.ψ (L t) f.1 w := by
      show (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (P t)) f).1 w = _
      rw [coe_rhoBF, ← hLP t]
    have h2 : B.ψ (-(symplOHF σ JS JT ξ₀ w (L t))) = Complex.exp (φ t) := by
      rw [hlam _ (by rw [map_neg, GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w _ (hL0 t), neg_zero]), map_neg]
      rfl
    show f.1 (w + L t) = Complex.exp (φ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f)
    rw [ev_apply, h1, ← h2, heisOF, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
      one_mul]
  rw [e]
  exact (φ.toRealLinearMap hφ).contDiff.cexp.mul
    (((ev _ _ w).restrictScalars ℝ).contDiff.comp (hF.comp (P.toRealLinearMap hP).contDiff))
end

section
open Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open Matrix (fromBlocks fromBlocks_multiply fromBlocks_one fromBlocks_apply₁₂ transpose_one transpose_apply)
open GlobalTheory.EisBL.DoubledParabolic (inFrame_mul inFrame_one)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
abbrev _root_.GlobalTheory.T.archimedean_chart_gaussian_invariant :=
  GlobalTheory.ThetaOfSmF.theta_of_smF_k

namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas
variable {d : SD_k σ} (L : LD_k d)
def pre_k (r : Fin d.n) (h : r ≠ L.i₀) : Fin L.n := ((L.rng r).1 h).choose
theorem em_pre_k (r : Fin d.n) (h : r ≠ L.i₀) : L.em (pre_k L r h) = r := ((L.rng r).1 h).choose_spec
theorem pre_em_k (k : Fin L.n) (h : L.em k ≠ L.i₀) : pre_k L (L.em k) h = k := L.inj (em_pre_k L _ h)
def padZ_k (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) := fun r c =>
  if hr : r = L.i₀ then 0 else if hc : c = L.i₀ then 0 else β (pre_k L r hr) (pre_k L c hc)
theorem one_em_k (k l : Fin L.n) :
    (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (L.em k) (L.em l) = (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) k l := by
  simp [Matrix.one_apply, L.inj.eq_iff]
theorem inFrame_j_nb_k {x : G2 σ L.Y} {β : Matrix (Fin L.n) (Fin L.n) (AE F E)}
    (hx : inFrame L.b x = fromBlocks 1 β 0 1) :
    inFrame d.b (L.j x) = fromBlocks 1 (padZ_k L β) 0 1 := by
  have hin := L.j_in x
  rw [hx] at hin
  have emb : ∀ u v : Fin L.n ⊕ Fin L.n, inFrame d.b (L.j x) (Sum.map L.em L.em u) (Sum.map L.em L.em v) =
      fromBlocks 1 β 0 1 u v := fun u v => by rw [← hin]; rfl
  have kl : ∀ v, inFrame d.b (L.j x) (Sum.inl L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inl L.i₀) v ∧
      inFrame d.b (L.j x) v (Sum.inl L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inl L.i₀) :=
    fun v => L.j_out x _ (by simp) v
  have kr : ∀ v, inFrame d.b (L.j x) (Sum.inr L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inr L.i₀) v ∧
      inFrame d.b (L.j x) v (Sum.inr L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inr L.i₀) :=
    fun v => L.j_out x _ (by simp) v
  ext (r | r) (c | c)
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kl _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kl _).2]; simp [hr]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inl k) (Sum.inl l)
    simp only [Sum.map_inl, Matrix.fromBlocks_apply₁₁] at this ⊢
    rw [this, one_em_k]
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kl _).1]; simp [padZ_k]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kr _).2]; simp [padZ_k]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inl k) (Sum.inr l)
    simp only [Sum.map_inl, Sum.map_inr, fromBlocks_apply₁₂] at this ⊢
    rw [this]
    simp [padZ_k, ComplexParameterFamilyContinuity.em_ne_k, pre_em_k]
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kr _).1]; simp
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kl _).2]; simp
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inr k) (Sum.inl l)
    simp only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₂₁] at this ⊢
    rw [this]
    simp
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kr _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kr _).2]; simp [hr]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inr k) (Sum.inr l)
    simp only [Sum.map_inr, Matrix.fromBlocks_apply₂₂] at this ⊢
    rw [this, one_em_k]
theorem padCond_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {β : Matrix (Fin L.n) (Fin L.n) (AE F E)} (hβ : β ∈ nA σ L.Y L.b) (k l : Fin L.n) :
    β l k = -(((ε : ℤ) : AE F E) * cA σ (β k l)) := by
  revert k l
  induction hβ using AddSubgroup.closure_induction with
  | mem β h =>
    obtain ⟨x, hx⟩ := h
    have hmem : padZ_k L β ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨L.j x, inFrame_j_nb_k L hx⟩
    have hc := (kunf.mem_nA_iff hε _).1 hmem
    intro k l
    have := congrFun (congrFun hc (L.em k)) (L.em l)
    simpa [padZ_k, ComplexParameterFamilyContinuity.em_ne_k, pre_em_k, transpose_apply, smul_eq_mul] using this
  | zero => intro k l; simp
  | add β β' _ _ h h' => intro k l; rw [Matrix.add_apply, Matrix.add_apply, h, h', map_add (f := _), mul_add, neg_add]
  | neg β _ h => intro k l; rw [Matrix.neg_apply, Matrix.neg_apply, h, map_neg, mul_neg]
theorem sig_delta_k (hB : GoodK σ d.B) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E}
    (hcf : ∃ (x : d.G) (A' : Matrix (Fin d.n) (Fin d.n) (AE F E)),
      inFrame d.b x = fromBlocks 1 (aB_k L δ 1) 0 A') :
    σ δ = ((-(ε : ℤ) : ℤ) : E) * δ := by
  have cA_inclR (x : E) : cA σ (inclR (AF F) x) = inclR (AF F) (σ x) := by
    show map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
    rw [map_tmul, AlgHom.id_apply]
  obtain ⟨x, A', hx⟩ := hcf
  have inv : ∀ z, cA σ (cA σ z) = z := by
    intro z
    have hσ := kunf.sigma_invol_k d.B hB
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show map (AlgHom.id (AF F) (AF F)) σ
        (map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
      rw [map_tmul, map_tmul, AlgHom.id_apply, AlgHom.id_apply, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have h := kunf.frame_eq hε x
  rw [hx] at h
  have h1 : (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, fromBlocks_multiply,
    transpose_one, Matrix.transpose_zero, h1, h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add] at h
  obtain ⟨-, h2, -, h4⟩ := Matrix.fromBlocks_inj.1 h
  have hA : A' = 1 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at this
    rw [← inv (A' i j), this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hA, h1, transpose_one, Matrix.one_mul, Matrix.mul_one] at h4
  have he := congrFun (congrFun h4 L.i₀) L.i₀
  simp [aB_k, cA_inclR] at he
  have e2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := eps_sq ε
  have h5 : ((ε : ℤ) : E) * σ δ + δ = 0 := by
    apply kfour.inclR_injective (F := F)
    simpa [cA_inclR] using he
  push_cast
  linear_combination ((ε : ℤ) : E) * h5 - σ δ * e2
def ins_k (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    Matrix (Fin d.n) (Fin d.n) (AE F E) := fun r c =>
  if hr : r = L.i₀ then (if hc : c = L.i₀ then x.1.2 • inclR (AF F) δ else x.1.1 (pre_k L c hc))
  else (if hc : c = L.i₀ then -(e * cA σ (x.1.1 (pre_k L r hr))) else x.2 (pre_k L r hr) (pre_k L c hc))
theorem continuous_ins_k (e : AE F E) (δ : E) : Continuous (ins_k L e δ) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  unfold ins_k
  have hcA := GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA (σ := σ)
  by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;> simp only [hr, hc, dite_true, dite_false] <;> fun_prop
theorem ins_mem_k (hB : GoodK σ d.B) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E}
    (hδ : σ δ = ((-(ε : ℤ) : ℤ) : E) * δ) (b : Fin L.n → AE F E) (a : AF F) {β : Matrix (Fin L.n) (Fin L.n) (AE F E)}
    (hβ : β ∈ nA σ L.Y L.b) : ins_k L (((ε : ℤ) : AE F E)) δ ((b, a), β) ∈ nA σ d.Y d.b := by
  have cA_inclR (x : E) : cA σ (inclR (AF F) x) = inclR (AF F) (σ x) := by
    show map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [kunf.mem_nA_iff hε]
  have e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := eps_sq ε
  have cε : cA σ (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E) := map_intCast _ _
  have inv : ∀ z, cA σ (cA σ z) = z := by
    intro z
    have hσ := kunf.sigma_invol_k d.B hB
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show map (AlgHom.id (AF F) (AF F)) σ
        (map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
      rw [map_tmul, map_tmul, AlgHom.id_apply, AlgHom.id_apply, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  ext r c
  simp only [transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc
  · simp only [ins_k, dite_true]
    rw [map_smul, cA_inclR, hδ, map_mul, map_intCast, Algebra.smul_def, Algebra.smul_def]
    push_cast
    linear_combination (-(algebraMap (AF F) (AE F E) a * inclR (AF F) δ)) * e2
  · simp [ins_k, hc]
  · simp only [ins_k, hr, dite_true, dite_false]
    rw [map_neg, map_mul, cε, inv]
    linear_combination (-(b (pre_k L r hr))) * e2
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    simp only [ins_k, hr, hc, dite_false, pre_em_k]
    exact padCond_k L hε hβ k l
theorem ins_left_k (_hB : GoodK σ d.B) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = ((-(ε : ℤ) : ℤ) : E) * δ) (β : nA σ d.Y d.b) :
    ins_k L (((ε : ℤ) : AE F E)) δ (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic δ (β.1 L.i₀ L.i₀)),
      (C4.prj_k L β).1) =
      β.1 := by
  have hc := (kunf.mem_nA_iff hε β.1).1 β.2
  have e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := eps_sq ε
  have hk : (-(ε : ℤ)) * (-(ε : ℤ)) = 1 := by rw [neg_mul_neg]; exact eps_sq ε
  ext r c
  rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc'
  · simp only [ins_k, dite_true]
    have h0 := congrFun (congrFun hc L.i₀) L.i₀
    simp only [transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0
    refine (eig_AE_k d.ok.good hk hδ0 hδ ?_).symm
    push_cast
    linear_combination ((ε : ℤ) : AE F E) * h0 - cA σ (β.1 L.i₀ L.i₀) * e2
  · obtain ⟨l, rfl⟩ := (L.rng c).1 hc'
    simp [ins_k, ComplexParameterFamilyContinuity.em_ne_k, pre_em_k]
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    have h0 := congrFun (congrFun hc L.i₀) (L.em k)
    simp only [transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0
    simp only [ins_k, hr, dite_true, dite_false, pre_em_k]
    exact h0.symm
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc'
    simp only [ins_k, hr, hc', dite_false, pre_em_k, C4.prj_val_k,
      Matrix.submatrix_apply]
theorem ins_pb_k (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    (fun j => ins_k L e δ x L.i₀ (L.em j)) = x.1.1 := by
  funext j
  simp [ins_k, ComplexParameterFamilyContinuity.em_ne_k, pre_em_k]
theorem ins_pa_k {δ : E} (hδ0 : δ ≠ 0) (e : AE F E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F
  E)) :
    linearFormAdelic δ (ins_k L e δ x L.i₀ L.i₀) = x.1.2 := by
  simp only [ins_k, dite_true]
  exact ellA_smul_inclR hδ0 _
theorem ins_sub_k (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    (ins_k L e δ x).submatrix L.em L.em = x.2 := by
  ext k l
  simp [ins_k, ComplexParameterFamilyContinuity.em_ne_k, pre_em_k]
theorem pEquiv0_k {δ : E} (hδ0 : δ ≠ 0)
    (hcf : ∃ (x : d.G) (A' : Matrix (Fin d.n) (Fin d.n) (AE F E)),
      inFrame d.b x = fromBlocks 1 (aB_k L δ 1) 0 A') :
    ∃ P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b),
      (∀ β, P β = (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)),
        C4.prj_k L β)) ∧
      ∀ β, β ∈ nF σ d.Y d.b ↔ (((fun j => β.1 L.i₀ (L.em j)) ∈ L.ratV ∧
        linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀) ∈ (algebraMap F (AF F)).range.toAddSubgroup) ∧
          C4.prj_k L β ∈ nF σ L.Y L.b) := by
  have hB := d.ok.good
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hδ := sig_delta_k L hB hε hcf
  let fwd : nA σ d.Y d.b → ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b :=
    fun β => (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)),
      C4.prj_k L β)
  let bwd : ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b → nA σ d.Y d.b :=
    fun x => ⟨ins_k L (((ε : ℤ) : AE F E)) δ (x.1, x.2.1), ins_mem_k L hB hε hδ x.1.1 x.1.2 x.2.2⟩
  have hleft : ∀ β, bwd (fwd β) = β := fun β => Subtype.ext (ins_left_k L hB hε hδ0 hδ β)
  have hright : ∀ x, fwd (bwd x) = x := by
    rintro ⟨⟨b, a⟩, β''⟩
    refine Prod.ext (Prod.ext (ins_pb_k L _ δ _) (ins_pa_k L hδ0 _ _)) (Subtype.ext ?_)
    rw [C4.prj_val_k]
    exact ins_sub_k L _ δ _
  let P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) :=
    { toFun := fwd
      invFun := bwd
      left_inv := hleft
      right_inv := hright
      map_add' := fun β β' => by
        refine Prod.ext (Prod.ext ?_ ?_) (map_add (C4.prj_k L) β β')
        · funext j
          rfl
        · show linearFormAdelic (F := F) δ ((β + β').1 L.i₀ L.i₀) = linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀) +
            linearFormAdelic (F := F) δ (β'.1 L.i₀ L.i₀)
          rw [← map_add (f := _)]
          rfl
      continuous_toFun := by
        refine Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_
        · exact continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp continuous_subtypeVal)
        · exact (continuous_ellA δ).comp ((continuous_apply _).comp ((continuous_apply _).comp continuous_subtypeVal))
        · exact continuous_induced_rng.2 (continuous_subtypeVal.matrix_submatrix _ _)
      continuous_invFun := by
        refine Continuous.subtype_mk ((continuous_ins_k L _ δ).comp ?_) _
        exact continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd) }
  refine ⟨P, fun β => rfl, fun β => ?_⟩
  constructor
  · intro hβ
    obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
    refine ⟨⟨ComplexParameterFamilyContinuity.mem_ratVec.2 ⟨fun j => T L.i₀ (L.em j), ?_⟩, ?_⟩,
      kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩⟩
    · funext j
      rw [hT]
      rfl
    · obtain ⟨f, hf⟩ := ellA_inclR (F := F) δ (T L.i₀ L.i₀)
      refine ⟨f, ?_⟩
      rw [hT]
      exact hf.symm
    · rw [C4.prj_val_k, hT]
      rfl
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨v, hv⟩ := ComplexParameterFamilyContinuity.mem_ratVec.1 h1
    obtain ⟨f, hf⟩ := h2
    obtain ⟨T'', hT''⟩ := kunf.mem_nF_iff.1 h3
    have hv' : ∀ j, β.1 L.i₀ (L.em j) = inclR (F := F) (AF F) (v j) := fun j => (congrFun hv j).symm
    have hT2 : ∀ k l,
      (C4.prj_k L β).1 k l = inclR (F := F) (AF F) (T'' k l) := fun k l =>
      by rw [hT'']; rfl
    refine kunf.mem_nF_iff.2 ⟨Matrix.of fun r c => if hr : r = L.i₀ then (if hc : c = L.i₀ then f • δ else v (pre_k L c
      hc))
      else (if hc : c = L.i₀ then -(((ε : ℤ) : E) * σ (v (pre_k L r hr))) else T'' (pre_k L r hr) (pre_k L c hc)), ?_⟩
    conv_lhs => rw [← ins_left_k L hB hε hδ0 hδ β]
    ext r c
    by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;>
      simp only [ins_k, incM, Matrix.map_apply, Matrix.of_apply, hr, hc, dite_true, dite_false]
    · rw [inclR_smul', ← hf]
    · exact hv' _
    · have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
        show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [hv', map_neg, map_mul, map_intCast, cA_inclR]
    · exact hT2 _ _
end PositivityTheory.SiegelWeilFormula.Act.C5.Meas

section
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem pEquiv_k (h : Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b),
      (∀ β, P β = ((pb_k L β, pa_k L δ β), C4.prj_k L β)) ∧
      ∀ β, β ∈ nF σ d.Y d.b ↔ (pb_k L β ∈ L.ratV ∧ pa_k L δ β ∈ fA F) ∧
        C4.prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨P, h1, h2⟩ := Meas.pEquiv0_k L h.δ0 ⟨cM (0, 1), by
    obtain ⟨A', hA'⟩ := h.cf (0, 1)
    refine ⟨A', ?_⟩
    rw [hA']
    have hu : uA_k L (0 : Fin L.n → AE F E) = 1 := by simp [uA_k]
    rw [hu]⟩
  exact ⟨P, h1, h2⟩
theorem lam_map_k {lam : Measure (nA σ d.Y d.b)} [lam.IsAddHaarMeasure] {ν : Measure (Fin L.n → AE F
  E)} [ν.IsAddHaarMeasure]
    {lam' : Measure (nA σ L.Y L.b)} [lam'.IsAddHaarMeasure] (P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ
      L.Y L.b)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ lam.map P = c • ((ν.prod (lamA F)).prod lam') := by
  have : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  have := P.isAddHaarMeasure_map lam
  have : SFinite ν := inferInstance
  have : SFinite lam' := inferInstance
  have : SFinite (lamA F) := inferInstance
  have : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : SFinite (ν.prod (lamA F)) := inferInstance
  have : ((ν.prod (lamA F)).prod lam').IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor (lam.map P) ((ν.prod (lamA F)).prod lam') : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _
theorem kap_eq_k {ν : Measure (Fin L.n → AE F E)} [ν.IsAddHaarMeasure] {κ : Measure ((Fin L.n → AE F E) × AF F)}
    [κ.IsAddHaarMeasure] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ κ = c • (ν.prod (lamA F)) := by
  have : SFinite ν := inferInstance
  have : SFinite (lamA F) := inferInstance
  have : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor κ (ν.prod (lamA F)) : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _
end PositivityTheory.SiegelWeilFormula.Act.C5
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {d : SD_k σ} {R : RD_k d} {L : LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
def kom_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) : d.G
  :=
  L.j (nb' p.2) * uM p.1 * (L.j (nb' p.2))⁻¹ * (uM p.1)⁻¹
variable (L) in
def tau_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (δ : E) (p : (Fin L.n → AE F E) × nA σ L.Y
  L.b) :
    (Fin L.n → AE F E) × AF F :=
  (fun k => inFrame d.b (kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr (L.em k)),
    ellA δ (inFrame d.b (kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr L.i₀)))
variable (L) in
def Du_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  (uA_k L (-u))ᵀ.map (cA σ)
theorem frame_uM_k (h : Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F
  E) :
    inFrame d.b (uM u) = fromBlocks (uA_k L u) 0 0 (Du_k L u) :=
      by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha,
    lr_of_k ha
    (uA_mul_neg_k L u)]
  rfl
theorem Du_mul_k (u : Fin L.n → AE F E) : Du_k (σ := σ) L u * Du_k L (-u) = 1 := by
  unfold Du_k
  rw [← Matrix.map_mul, ← Matrix.transpose_mul, neg_neg,
    uA_mul_neg_k L u]
  ext i j
  simp [Matrix.one_apply, Matrix.map_apply]
theorem uM_neg'_k (h : Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F
  E) : uM (-u) = (uM u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (KAway.inFrame_inj_k d ?_)
  rw [inFrame_mul, frame_uM_k h, frame_uM_k h,
    inFrame_one, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    uA_mul_neg_k, Du_mul_k, fromBlocks_one]
theorem continuous_uA_k : Continuous (uA_k (σ := σ) L) := by
  unfold uA_k
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
      fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]; exact (continuous_apply j).smul continuous_const
theorem continuous_frame_uM_k : Continuous fun u : Fin L.n → AE F E =>
    (fromBlocks (uA_k L u) 0 0 (Du_k L u) : Matrix (Fin
      d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
  refine Continuous.matrix_fromBlocks continuous_uA_k continuous_const continuous_const ?_
  unfold Du_k
  exact ((continuous_uA_k.comp continuous_neg).matrix_transpose).matrix_map
    (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
theorem frame_kom_k (h : Hyp_k L nb uM nb' w₁ cM δ) (p : (Fin L.n → AE
  F E) × nA σ L.Y L.b) :
    inFrame d.b (kom_k L uM nb' p) = inFrame d.b (L.j (nb' p.2)) * fromBlocks
      (uA_k L p.1) 0 0 (Du_k L p.1) *
      inFrame d.b (L.j (nb' (-p.2))) * fromBlocks (uA_k L
        (-p.1)) 0 0 (Du_k L (-p.1)) := by
  unfold kom_k
  rw [← uM_neg'_k h, ← map_inv, ← kunf.nb_neg h.nb', inFrame_mul,
    inFrame_mul,
    inFrame_mul, frame_uM_k h, frame_uM_k h]
theorem continuous_kom_k (h : Hyp_k L nb uM nb' w₁ cM δ) : Continuous
  fun p => inFrame d.b (kom_k L uM nb' p) := by
  have hj :=
    (GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame d.b).comp (L.cont.comp (kunf.continuous_nb h.nb'))
  simp only [frame_kom_k h]
  exact (((hj.comp continuous_snd).matrix_mul (continuous_frame_uM_k.comp continuous_fst)).matrix_mul
    ((hj.comp continuous_neg).comp continuous_snd)).matrix_mul ((continuous_frame_uM_k.comp continuous_neg).comp
      continuous_fst)
theorem continuous_tau_k (h : Hyp_k L nb uM nb' w₁ cM δ) : Continuous
  (tau_k L uM nb' δ) := by
  have hk := continuous_kom_k h
  refine Continuous.prodMk (continuous_pi fun k => hk.matrix_elem _ _) ?_
  exact (IsModuleTopology.continuous_of_linearMap (R := AF F) (ellA δ)).comp (hk.matrix_elem _ _)
theorem Du_neg_row_k (u : Fin L.n → AE F E) (k : Fin d.n) :
    Du_k L (-u) L.i₀ k = if k = L.i₀ then 1 else 0 := by
  unfold Du_k
  rw [neg_neg, Matrix.map_apply, transpose_apply]
  by_cases hk : k = L.i₀
  · subst hk
    simp [uA_k, Matrix.add_apply, Matrix.sum_apply,
      fun j => ComplexParameterFamilyContinuity.em_ne_k L j]
  · simp [uA_k, Matrix.add_apply, Matrix.sum_apply,
      hk, Ne.symm hk]
theorem sM_zero'_k : sM_k R L 0 = 1 := by
  apply KAway.inFrame_inj_k d
  rw [inFrame_sM'_k, inFrame_one]
  have : sB_k R L 0 = 0 :=
    by simp [sB_k]
  rw [this, bMat_k, fromBlocks_one]
theorem cM_zero'_k (h : Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F
  E) : cM (u, 0) = uM u := by
  apply KAway.inFrame_inj_k d
  rw [inFrame_cM_k h, frame_uM_k h]
  simp [aB_k, Du_k]
theorem move_k (h : Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E)
  (β'' : nA σ L.Y L.b) (b : Fin L.n → AE F E) (a : AF F) :
    L.j (nb' β'') * (sM_k R L b * cM (u, a)) =
      sM_k R L (b + (tau_k L uM nb' δ (u, β'')).1) * cM (u,
        a + (tau_k L uM nb' δ (u, β'')).2) * L.j (nb' β'') := by
  obtain ⟨B, A, hBA⟩ := j_move_k h u β''
  suffices hτ : tau_k L uM nb' δ (u, β'') = (B, A) by rw [hτ]; exact hBA b a
  have e0 := hBA 0 0
  rw [sM_zero'_k, one_mul, cM_zero'_k h, zero_add, zero_add] at e0
  have hk : kom_k L uM nb' (u, β'') = sM_k R L B * cM (u,
    A) * (uM u)⁻¹ := by
    show L.j (nb' β'') * uM u * (L.j (nb' β''))⁻¹ * (uM u)⁻¹ = _
    rw [e0, mul_inv_cancel_right]
  have hf : inFrame d.b (kom_k L uM nb' (u, β'')) =
      fromBlocks 1 (aB_k L δ A * Du_k L (-u) +
        sB_k R L B) 0 1 := by
    rw [hk, ← uM_neg'_k h, inFrame_mul,
      inFrame_mul, inFrame_sM'_k,
      inFrame_cM_k h, frame_uM_k h,
      bMat_k]
    rw [show (uA_k L (-u))ᵀ.map (cA σ) = Du_k L u from rfl]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
      uA_mul_neg_k, Du_mul_k]
    rw [Matrix.add_mul, Matrix.mul_assoc, Du_mul_k, Matrix.mul_one]
  have hrow : ∀ k,
    (aB_k L δ A * Du_k L (-u)) L.i₀ k = if k = L.i₀ then A •
    inclR (AF F) δ else 0 := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single L.i₀]
    · rw [Du_neg_row_k]; simp [aB_k]
    · intro m _ hm; simp [aB_k, Ne.symm hm]
    · simp
  refine Prod.ext (funext fun k => ?_) ?_
  · show inFrame d.b (kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr (L.em k)) = B k
    rw [hf, fromBlocks_apply₁₂, Matrix.add_apply, hrow, ite_eq_right (ComplexParameterFamilyContinuity.em_ne_k L
        k),
      zero_add, sB_i0em_k]
  · show ellA δ (inFrame d.b (kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr L.i₀)) = A
    rw [hf, fromBlocks_apply₁₂, Matrix.add_apply, hrow, ite_eq_left rfl,
      sB_i0i0_k, add_zero, map_smul, ellA_self h.δ0,
      smul_eq_mul, mul_one]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end
end
