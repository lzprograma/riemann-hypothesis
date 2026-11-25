module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPow
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.MeromorphicOnOfWeak
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.FrameSignEqHermitianSign
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.InFrameForm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.HolValueAtConstMulCpow
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasND
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SectionLinearFinsetSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThGramIncM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThInclRInjective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThMSymmApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

/-! # SiegelWeilKwhitIwa: Consolidated global theta-kernel definitions and proofs (SiegelWeilKwhitIwa). -/
@[expose] public section

noncomputable section
open PositivityTheory.SiegelWeilFormula HeckeCharacterZeroLocus
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace PositivityTheory.SiegelWeilFormula.Khead
def basis2_k {B : Base F E} (h : _root_.UpperTheory.TP.W.GoodK σ B) : Module.Basis (Fin 2) F E :=
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.cm.2.2.1]; norm_num)
  Module.finBasisOfFinrankEq F E h.cm.2.2.1

theorem headOf_k : HeadOf_k := by
  intro hBL hSec hStrong hMain F E _ _ _ _ _ σ B m n A Y r s r' s' χ κ _ dd om S l b K a μ D Φ H
  let d : SD_k σ :=
    { B := B, m := m, n := n, A := A, Y := Y, r := r, s := s, χ := χ, κ := κ, dd := dd, om := om,
      S := S, l := l, b := b, K := K, a := a, μ := μ, D := D, bs := basis2_k H.good,
      ok := ⟨H.good, H.hm, H.hn, H.aniso, H.sign.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩),
        H.hecke, H.res, H.dbl, H.frame, H.stdK, H.hgt, H.haar, H.dom⟩ }
  have hK : d.KFin Φ := ⟨H.sch, H.fin⟩
  have hY : Y.IsHerm σ B r' s' ∨ Y.IsSkew σ B r' s' := H.sign.elim (fun h => .inr h.2) (fun h => .inl h.2)
  obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ B n Y r' s' H.good H.hn hY χ H.hecke m H.res b K a H.frame H.stdK H.hgt
    (s0 m n) (d.sec0 Φ) (hSec F E σ d Φ hK)
  intro x
  have hfl (z : ℂ) : (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ y) =
      GlobalTheory.ThK.Dbl.flat a (d.sec0 Φ) (s0 m n) z :=
    funext fun y => by
      simp only [SD_k.Ht, GlobalTheory.ThK.Dbl.flat, Real.coe_toNNReal _ (hgt_nonneg d.ok.hgt y)]; rfl
  have hmer := meromorphicOn_of_weak hw x
  have hext : IsExtAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (Ê · x) :=
    ⟨Set.univ, trivial, isRightDomain_univ, hmer, t,
      fun z hz => by simp only [SD_k.eis, hfl z]; exact (hsum z hz x).tsum_eq.symm⟩
  obtain ⟨H', hext', han, hval⟩ :=
    hMain F E σ d H.hnm (fun Φ' hΦ' => hStrong F E σ d ⟨r', s', hY⟩ _ _ (hSec F E σ d Φ' hΦ')) Φ hK x
  have hloc : Function.update (Ê · x) (s0 m n) (d.I Φ x) =ᶠ[𝓝 (s0 m n)] H' := by
    filter_upwards [eventually_nhdsWithin_iff.1 (hext'.eventuallyEq hext)] with z hz
    by_cases e : z = s0 m n
    · subst e; rw [Function.update_self]; exact hval.symm
    · rw [Function.update_of_ne e]; exact (hz e).symm
  refine ⟨Function.update (Ê · x) (s0 m n) (d.I Φ x), fun z _ => (hmer z trivial).update _ _,
    ⟨max t (s0 m n).re, fun z hz => ?_⟩, han.congr hloc.symm, Function.update_self _ _ _⟩
  rw [Function.update_of_ne (fun e => by subst e; exact lt_irrefl _ (lt_of_le_of_lt (le_max_right _ _) hz))]
  exact hsum z (lt_of_le_of_lt (le_max_left _ _) hz) x
end PositivityTheory.SiegelWeilFormula.Khead

namespace PositivityTheory.SiegelWeilFormula.KWhit
def IsLevi_k (d : SD_k σ) (x : d.G) : Prop :=
  ∃ t u : GL (Fin d.n) (AE F E), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1

def IsPureBy_k {d : SD_k σ} (R : RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) : Prop :=
  (∀ v, IsLocallyConstant (gf v) ∧ HasCompactSupport (gf v)) ∧
    (∀ᶠ v in cofinite, gf v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) * ∏ᶠ v, gf v (fun k => SiegelWeilU.evalV F v (d.crd X k).2)

def IsPureT_k {d : SD_k σ} (R : RD_k d) (Φ : d.Fn) : Prop := ∃ P g, IsPureBy_k R Φ P g

def PureSpan_k : Prop := TAll_k → FockMem_k → PolyKFin_k → ForAllSD fun d => ∀ (R : RD_k d) Φ,
  d.KFin Φ → d.T Φ ∈ R.fock →
    ∃ (k : ℕ) (c : Fin k → ℂ) (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i) ∧ IsPureT_k R (Φs i)) ∧ Φ = ∑ i, c i • Φs i

def CellFormula_k : Prop := TAll_k → ForAllSD fun {F _ _ _ _ _ _ _} d => ∀ ν, d.IsCov ν → ∀ ε w, d.IsW ε w →
  ∀ Φ ∈ d.sch, ∀ (g x : d.G) (β : d.Mn), inFrame d.b g = Matrix.fromBlocks 1 β 0 1 →
    d.sec0 Φ (w * g * x) = ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram Z Z))) * d.T (d.om x Φ) Z ∂ν

theorem incM_mul_inv_k (d : SD_k σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := Krd.bb_k d
theorem incM_inv_mul_k (d : SD_k σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := Krd.bb'_k d
theorem inFrame_mul_k (d : SD_k σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y :=
  d.inFrame_mul x y
theorem matrixRep_eq_frameConj_inFrame (d : SD_k σ) (x : d.G) :
    mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  exact PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.matrixRep_eq_frameConj_inFrame d
    x
theorem inFrame_injective_k (d : SD_k σ) : Function.Injective (inFrame (σ := σ) (Y := d.Y) d.b) :=
  fun _ _ h => d.inFrame_inj h
theorem om_mem_sch_k (d : SD_k σ) (g : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om g Φ ∈ d.sch := d.om_sch g Φ h
theorem constantTerm_mul_right (d : SD_k σ) (Φ : d.Fn) (g k : d.G) : d.sec0 Φ (g * k) = d.sec0 (d.om k Φ) g := by
  simp [SD_k.sec0, map_mul, mul_apply_eq_comp]
theorem a_mul_K_k (d : SD_k σ) (g k : d.G) (hk : k ∈ d.K) : d.a (g * k) = d.a g := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := d.ok.hgt.iwa g
  rw [mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']
theorem kfin_om_k (d : SD_k σ) {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) : d.KFin (d.om k Φ) := by
  refine ⟨d.om_sch k Φ hΦ.1, ?_⟩
  have := hΦ.2
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  exact Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, by simp [map_mul, mul_apply_eq_comp]⟩

private theorem frame_form_eps (d : SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  rw [show (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) from by ext _ _; exact (th_cA_incl _).symm,
    Krd.dbl_incM_k, show (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) =
      incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) from by simp only [incM, Matrix.map_mul, Matrix.transpose_map], hε]
  simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1; ext _ _
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]; split_ifs <;> simp

theorem frame_form_k (d : SD_k σ) : ∃ C' : d.Mn,
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame; exact ⟨((ε : ℤ) : AE F E) • 1, frame_form_eps d ε hε⟩

private theorem rel_frame_k (d : SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (y : d.G) :
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 * (inFrame d.b y).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  have := form_conj_in (cA σ).toRingHom (incM_mul_inv_k d)
    (y.2 : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = _)
  have hf : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := frame_form_eps d ε hε
  rwa [hf] at this

private theorem par_E1_k (d : SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ tb : GL (Fin d.n) E, (inFrame d.b p).toCols₁ =
      (Matrix.fromRows 1 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) *
        (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame; refine ⟨tb, ?_⟩
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have hcol (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : M * E1 = M.toCols₁ := by
    ext i j; simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := by
    rw [hcol, show (incM F d.b.1).toCols₁ = incM F d.b.1.toCols₁ from Matrix.ext fun _ _ => rfl, htb,
      show incM F (diagCols (Fin d.n) * tb.1) = incM F (diagCols (Fin d.n)) * incM F tb.1 from
        Matrix.map_mul (f := inclR (AF F))]
    congr 1; ext i j; cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite]
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  rw [← hcol]
  calc inFrame d.b p * E1 = incM F (d.b⁻¹).1 * (mat2 p * (incM F d.b.1 * E1)) := by
        show incM F (d.b⁻¹).1 * mat2 p * incM F d.b.1 * E1 = _; simp only [Matrix.mul_assoc]
    _ = incM F (d.b⁻¹).1 * ((DC * t.1) * incM F tb.1) := by
        rw [hb, ← Matrix.mul_assoc (mat2 p), show mat2 p * DC = DC * t.1 from hp]
    _ = (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
        rw [hdc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [incM_inv_mul_k d, Matrix.one_mul]

theorem parabolic_lowerLeft_block_zero (d : SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    (inFrame d.b p).toBlocks₂₁ = 0 := by
  obtain ⟨tb, key⟩ := par_E1_k d p t hp; ext i j
  simpa [Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type] using
    congrFun (congrFun key (Sum.inr i)) j

theorem par_decomp_k (d : SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ (n0 m0 : d.G) (β₀ : d.Mn),
      inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1 ∧ IsLevi_k d m0 ∧ p = n0 * m0 := by
  have h21 := parabolic_lowerLeft_block_zero d p t hp
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁; set B := g.toBlocks₁₂; set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_inv_mul_k d, Matrix.det_one]⟩)
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 ((hBi.mul (Units.isUnit p.1)).mul hBm)
  have hA := isUnit_of_mul_isUnit_left hdet; have hD := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2
    (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := frame_form_k d
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  have hgf := form_conj_in (cA σ).toRingHom (incM_mul_inv_k d)
    (p.2 : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = _)
  rw [hC''] at hgf
  have hMdf := block_diag_form (cA σ).toRingHom A B D C' (by
    change (inFrame d.b p)ᵀ * _ * (inFrame d.b p).map (cA σ).toRingHom = _ at hgf; rwa [← hg, hgb] at hgf)
  rw [← hC''] at hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let m0 : d.G := ⟨hM0u.unit, by
    show (hM0u.unit : Matrix _ _ (AE F E))ᵀ * dbl (incM F d.Y.J) * (hM0u.unit : Matrix _ _ (AE F E)).map (cA σ) = _
    rw [IsUnit.unit_spec]; exact form_conj_out (cA σ).toRingHom (incM_mul_inv_k d) hMdf⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (hM0u.unit : Matrix _ _ (AE F E)) * incM F d.b.1 = Md
    rw [IsUnit.unit_spec]; simp only [← Matrix.mul_assoc, incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul_k d, Matrix.mul_one]
  refine ⟨p * m0⁻¹, m0, B * D⁻¹, ?_,
    ⟨((Matrix.isUnit_iff_isUnit_det A).2 hA).unit, ((Matrix.isUnit_iff_isUnit_det D).2 hD).unit,
      by rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]⟩, (inv_mul_cancel_right p m0).symm⟩
  have e := inFrame_mul_k d (p * m0⁻¹) m0; rw [inv_mul_cancel_right, hm0] at e
  apply (hMd.mul_left_inj).1
  rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]; simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]

theorem orb_n_k (hT : TAll_k) (d : SD_k σ) (T : d.nF_) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) (n0 : d.G)
    (β₀ : d.Mn) (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) :
    d.orb T (d.om n0 Ψ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T Ψ := by
  have hP := (hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn
  have hgr (g : UA σ d.A.J) (X : d.MxE) : d.gram (mat g⁻¹ * X) (mat g⁻¹ * X) = d.gram X X := by
    have hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
    simp only [SD_k.gram, Matrix.transpose_mul, hm]
    calc Xᵀ * (mat g⁻¹)ᵀ * incM F d.A.J * ((mat g⁻¹).map (cA σ) * X.map (cA σ))
        = Xᵀ * ((mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ)) * X.map (cA σ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [show (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J from (g⁻¹).2]
  have hph : -(⅟(2 : AF F) * d.tt (β₀ * ((-2 : ℤ) • T.1.1))) = d.tt (T.1.1 * β₀) := by
    have h1 : d.tt (β₀ * ((-2 : ℤ) • T.1.1)) = (-2 : AF F) * d.tt (T.1.1 * β₀) := by
      simp only [SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T.1.1]
      rw [zsmul_eq_mul]; push_cast; ring
    rw [h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]
  have hs (g : UA σ d.A.J) :
      (∑' X : {X : d.ME // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∑' X : {X : d.ME // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T Ψ (mat g⁻¹ * incM F X.1) := by
    rw [← tsum_mul_left]; exact tsum_congr fun X => by rw [hP, hgr, X.2, hph]
  simp only [SD_k.orb, hs, MeasureTheory.average]; exact integral_const_mul _ _

theorem int_n_k (d : SD_k σ) (nb : d.nA_ → d.G) (lam : Measure d.nA_) (𝓖 : Set d.nA_)
    (hcd : d.CD nb lam 𝓖) (T : d.nF_) (w n0 m0 : d.G) (β₀ : d.Mn)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) (f : d.G → ℂ) :
    ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
      d.B.ψ (d.tt (T.1.1 * β₀)) * ∫ β, f (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
  have : lam.IsAddHaarMeasure := hcd.2.1; let b₀ : d.nA_ := ⟨β₀, AddSubgroup.subset_closure ⟨n0, hn⟩⟩
  have hnb (β : d.nA_) : nb β * n0 = nb (b₀ + β) := inFrame_injective_k d (by
    rw [inFrame_mul_k, hcd.1 β, hn, hcd.1 (b₀ + β)]; simp [Matrix.fromBlocks_multiply, add_comm, b₀])
  have htt (β : d.nA_) : d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1) := by
    simp [SD_k.tt, Matrix.mul_add, Matrix.trace_add, map_add (f := _), b₀]
  calc ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
      = ∫ β, (fun β' : d.nA_ => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) *
          d.B.ψ (d.tt (T.1.1 * β₀)))) (b₀ + β) ∂lam := by
        congr 1; funext β; dsimp only
        rw [← hnb β, htt β, ← AddChar.map_add_eq_mul,
          show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]
        simp only [mul_assoc]
    _ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam :=
        integral_add_left_haar lam b₀ (fun β' : d.nA_ => f (w * nb β' * m0) *
          (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))
    _ = _ := by rw [← integral_const_mul]; congr 1; funext β; ring

namespace Ht
theorem levi_tu_k (d : SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1) : t.1ᵀ * u.1.map (cA σ) = 1 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have h := rel_frame_k d ε hε x; rw [hx] at h
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h
  exact h.2.1

theorem frame_iwa_k (d : SD_k σ) (g : d.G) : ∃ (D : GL (Fin d.n) (AE F E)) (k : d.G), k ∈ d.K ∧
    d.a g = ((absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ)⁻¹ ∧
    (inFrame d.b g).toBlocks₂₁ = D.1 * (inFrame d.b k).toBlocks₂₁ ∧
    (inFrame d.b g).toBlocks₂₂ = D.1 * (inFrame d.b k).toBlocks₂₂ := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  have h21 := parabolic_lowerLeft_block_zero d p t' hp
  obtain ⟨tb, hE1⟩ := par_E1_k d p t' hp
  have htl : (inFrame d.b p).toBlocks₁₁ = incM F (tb⁻¹).1 * t'.1 * incM F tb.1 := by
    ext i j; simpa [Matrix.toBlocks₁₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      ite_mul, Finset.sum_ite_eq] using congrFun (congrFun hE1 (Sum.inl i)) j
  set A := (inFrame d.b p).toBlocks₁₁; set B := (inFrame d.b p).toBlocks₁₂; set D₀ := (inFrame d.b p).toBlocks₂₂
  have hPb : inFrame d.b p = Matrix.fromBlocks A B 0 D₀ := by rw [← h21, Matrix.fromBlocks_toBlocks]
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hform := rel_frame_k d ε hε p; rw [hPb] at hform
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at hform
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hDA : D₀ᵀ * A.map (cA σ) = 1 := by
    have h3 := hform.2.2.1; rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h3
    simpa [smul_smul, hεε] using congrArg (fun M => ((ε : ℤ) : AE F E) • M) h3
  have hdet : D₀.det * cA σ A.det = 1 := by
    have := congrArg Matrix.det hDA
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      show (A.map (cA σ)).det = cA σ A.det from (AlgHom.map_det (cA σ) A).symm] at this
  have hDu : IsUnit D₀ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, hdet⟩)
  have hpk : inFrame d.b (p * k) = Matrix.fromBlocks (A * (inFrame d.b k).toBlocks₁₁ + B * (inFrame d.b k).toBlocks₂₁)
      (A * (inFrame d.b k).toBlocks₁₂ + B * (inFrame d.b k).toBlocks₂₂)
      (D₀ * (inFrame d.b k).toBlocks₂₁) (D₀ * (inFrame d.b k).toBlocks₂₂) := by
    rw [inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    rw [Matrix.fromBlocks_multiply, Matrix.zero_mul, zero_add, Matrix.zero_mul, zero_add]
  refine ⟨hDu.unit, k, hk, ?_, by rw [hpk]; exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _,
    by rw [hpk]; exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _⟩
  rw [d.ok.hgt.val p t' hp k hk]
  have hAt : A.det = (Matrix.GeneralLinearGroup.det t').1 := by
    rw [htl, Matrix.det_mul, Matrix.det_mul]
    have hinv : (incM F (tb⁻¹).1).det * (incM F tb.1).det = 1 := by
      rw [← Matrix.det_mul, show incM F (tb⁻¹).1 * incM F tb.1 = 1 by
        simp only [incM, ← Matrix.map_mul, Units.inv_mul]
        exact Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]
    simp only [Matrix.GeneralLinearGroup.val_det_apply]; linear_combination t'.1.det * hinv
  have hU : Matrix.GeneralLinearGroup.det hDu.unit *
      GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det t') = 1 := by
    ext; simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec,
      GlobalTheory.Doubling.conjUnit, Units.coe_map]
    change D₀.det * sigR (AF F) σ t'.1.det = 1
    rw [sigR_eq_cA, ← Matrix.GeneralLinearGroup.val_det_apply, ← hAt]; exact hdet
  have := congrArg (absE F E) hU; rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at this
  rw [eq_inv_of_mul_eq_one_right this, NNReal.coe_inv]

theorem bottom_rows_k (d : SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1)
    (nb : d.nA_ → d.G) (hnb : IsNMap d.b nb) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) (β : d.nA_) :
    (inFrame d.b (w * nb β * x)).toBlocks₂₁ = (((ε : ℤ) : AE F E) • t.1) ∧
    (inFrame d.b (w * nb β * x)).toBlocks₂₂ = (((ε : ℤ) : AE F E) • (β.1 * u.1)) := by
  rw [inFrame_mul_k, inFrame_mul_k, hw, hnb β, hx]
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  constructor <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_eq,
    Finset.mul_sum, mul_assoc]
end Ht

theorem rel_nA_cond_k (d : SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (β : d.nA_) :
    β.1ᵀ + ((ε : ℤ) : AE F E) • β.1.map (cA σ) = 0 := by
  obtain ⟨β, hβ⟩ := β; show βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0
  induction hβ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hx; have h := rel_frame_k d ε hε y; rw [hy] at h
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.fromBlocks_inj] at h
    rw [add_comm]; have h4 := h.2.2.2; rwa [Matrix.smul_mul, Matrix.one_mul] at h4
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.transpose_add, Matrix.map_add _ (map_add (cA σ)), smul_add]
    calc _ = (xᵀ + ((ε : ℤ) : AE F E) • x.map (cA σ)) + (yᵀ + ((ε : ℤ) : AE F E) • y.map (cA σ)) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  | neg x _ hx => rw [Matrix.transpose_neg, Matrix.map_neg _ (map_neg (cA σ)), smul_neg, ← neg_add, hx, neg_zero]

private theorem frameSign_eq (d : SD_k σ) (hσ : ∀ x, σ (σ x) = x) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (c : E)
    (hc : d.Y.J.map σ = c • d.Y.Jᵀ) (i : Fin d.n) : ((ε : ℤ) : E) = c := by
  have hD : (dbl d.Y.J).map σ = c • (dbl d.Y.J)ᵀ := by
    simp only [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, hc,
      Matrix.map_neg _ (map_neg σ), Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero, Matrix.transpose_neg,
      smul_zero, smul_neg]
  have hbb : (d.b.1.map σ).map σ = d.b.1 := Matrix.ext fun _ _ => by simp [hσ]
  have h1 := congrArg σ.mapMatrix hε; simp only [map_mul, AlgHom.mapMatrix_apply, hD, hbb] at h1
  have h2 := congrArg Matrix.transpose h1
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.transpose_map] at h2
  rw [← Matrix.mul_assoc, hε] at h2
  have := congrFun (congrFun h2 (Sum.inr i)) (Sum.inl i); simp [Matrix.fromBlocks_map] at this
  have hε2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  calc ((ε : ℤ) : E) = ((ε : ℤ) : E) * (c * ((ε : ℤ) : E)) := by rw [this, mul_one]
    _ = c * (((ε : ℤ) : E) * ((ε : ℤ) : E)) := by ring
    _ = c := by rw [hε2, mul_one]

theorem rel_sign_k (d : SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((∀ i j, σ (d.Y.J j i) = -d.Y.J i j) → ε = -1) ∧ ((∀ i j, σ (d.Y.J j i) = d.Y.J i j) → ε = 1) := by
  have hσ := _root_.GlobalTheory.AdelicU.cm_conj_conj d.ok.good.cm; have i : Fin d.n := ⟨0, d.ok.hn⟩
  exact ⟨fun h => Units.ext (Int.cast_injective (α := E) (by
      simpa using frameSign_eq d hσ ε hε (-1) (by ext a b; simp [h b a]) i)),
    fun h => Units.ext (Int.cast_injective (α := E) (by
      simpa using frameSign_eq d hσ ε hε 1 (by ext a b; simp [h b a]) i))⟩

theorem rel_eta_k (d : SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ∃ η : E, η ≠ 0 ∧ σ η = -(((ε : ℤ) : E) * η) ∧ ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j := by
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have := (rel_sign_k d ε hε).1 hY; subst this; exact ⟨1, one_ne_zero, by simp, fun i j => by simp [hA.herm i j]⟩
  · have := (rel_sign_k d ε hε).2 hY; subst this
    obtain ⟨η, hη, hση⟩ := rel_anti d.ok.good.cm
    exact ⟨η, hη, by simp [hση], fun i j => by rw [map_mul, hση, hA.skew i j, neg_mul_neg]⟩

def Jd_k (d : SD_k σ) (η : E) : Matrix (Fin d.m) (Fin d.m) E := (η • d.A.J)ᵀ
structure Rel_k (d : SD_k σ) (R : RD_k d) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (T : d.nF_) (η : E)
    (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : d.nA_ → SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ) (g : InfinitePlace F → GL (Fin d.n) ℂ) : Prop where
  levi : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
  rat : T.1.1 = incM F T₀
  ne : η ≠ 0
  herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j
  hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : d.Mn)ᵀ)
  th : ∀ w y, θ w (Algebra.TensorProduct.map (SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)
  frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star
  gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1

def HeightDict_k : Prop := ForAllSD fun {F E _ _ _ _ _ _} d =>
  ∀ (R : RD_k d) x t u T η T₀ hOf θ fr g, Rel_k d R x t u T η T₀ hOf θ fr g →
  ∀ nb lam 𝓖, d.CD nb lam 𝓖 → ∀ ε w, d.IsW ε w →
  ∃ (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → SiegelWeilU.Fv F v ⊗[F] E)) (C : ℝ), 0 < C ∧
    (∀ v, (lv v).IsAddHaarMeasure) ∧ (∀ v, Gen.IsCO (L₁ v) ∧ Gen.IsCO (L₂ v)) ∧
    (∀ᶠ v in cofinite, (L₁ v : Set (Fin d.n → SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v ∧
      (L₂ v : Set (Fin d.n → SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
    ∀ β, 0 < Gen.nuA θ g lv L₁ L₂ (hOf β).1 ∧ d.a (w * nb β * x) = C * (Gen.nuA θ g lv L₁ L₂ (hOf β).1)⁻¹

def MeasDict_k : Prop := ForAllSD fun {F E _ _ _ _ _ σ} d =>
  ∀ (R : RD_k d) x t u T η T₀ hOf θ fr g, Rel_k d R x t u T η T₀ hOf θ fr g →
  (∀ nb lam 𝓖, d.CD nb lam 𝓖 → ∀ ν, SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν →
      MeasurableEmbedding hOf ∧ MeasurePreserving hOf lam ν) ∧
  ∀ μ νc, SiegelWeilU.SdW F E σ d.m (Jd_k d η) (AF F) d.B.ψ d.n μ → d.IsCov νc →
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ MeasurePreserving toMx μ νc

def ThetaDict_k : Prop := ForAllSD fun {F E _ _ _ _ _ σ} d =>
  ∀ (η : E), η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ μH 𝓕, SiegelWeilU.IsHaarH F E σ d.m (Jd_k d η) μH ∧ SiegelWeilU.IsFDH F E σ d.m (Jd_k d η) μH 𝓕 ∧
    ∀ (T : d.nF_) T₀, T.1.1 = incM F T₀ → ∀ Φ ∈ d.sch,
      d.orb T Φ = SiegelWeilU.meanC μH 𝓕 (SiegelWeilU.thetaS F E σ d.m (Jd_k d η) (fun Y => d.T Φ (toMx Y))
        {X | SiegelWeilU.gramE σ (Jd_k d η) X = Td η T₀})

def WhitAtC_k (c : ℂ) (d : SD_k σ) (Φ : d.Fn) (x : d.G) : Prop :=
  ∀ nb lam 𝓖, d.CD nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))

def IwaRedC_k : Prop := TAll_k → ∀ (c : ℂ), ForAllSD fun d => ∀ (Q : d.Fn → Prop),
  (∀ Φ, Q Φ → Φ ∈ d.sch) → (∀ Φ, Q Φ → ∀ k ∈ d.K, Q (d.om k Φ)) →
  (∀ Φ, Q Φ → ∀ x, IsLevi_k d x → WhitAtC_k c d Φ x) → ∀ Φ, Q Φ → ∀ x, WhitAtC_k c d Φ x

def LinRedC_k : Prop := TAll_k → ThetaCoef_k → LamBd_k → Unfold_k → SecK_k → ∀ (c : ℂ), ForAllSD fun d =>
  d.EisAll → ∀ (k : ℕ) (cs : Fin k → ℂ) (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i)) → ∀ x,
    (∀ i, WhitAtC_k c d (Φs i) x) → WhitAtC_k c d (∑ i, cs i • Φs i) x

def VacSpan_k : Prop := TAll_k → FockMem_k → PolyKFin_k → VacK_k → ForAllSD fun d => ∀ (R : RD_k d),
  ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ (k : ℕ) (cs : Fin k → ℂ) (Φs : Fin k → d.Fn),
    (∀ i, d.KFin (Φs i) ∧ d.T (Φs i) ∈ R.vac ∧ ∃ gf, IsPureBy_k R (Φs i) (fun _ => 1) gf) ∧ Φ = ∑ i, cs i • Φs i

def GenDictX_k : Prop := TAll_k → SiegelWeilDatumProperties → ForAllSD fun {F E _ _ _ _ _ σ} d =>
  ∀ (R : RD_k d) Φ, d.KFin Φ → ∀ P gf, IsPureBy_k R Φ P gf → ∀ x, IsLevi_k d x →
  ∀ nb lam 𝓖, d.CD nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
  ∃ (dd : ℕ) (J : Matrix (Fin d.m) (Fin d.m) E) (T' : Matrix (Fin d.n) (Fin d.n) E) (bs : Module.Basis (Fin dd) F E)
    (ψ : AddChar (AF F) ℂ) (θ : InfinitePlace F → (SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (l : InfinitePlace F → ℝ)
    (εs : InfinitePlace F → Fin d.m → Bool) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → SiegelWeilU.Fv F v ⊗[F] E))
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (SiegelWeilU.HermR (AF F) σ d.n)) (c : ℂ) (C : ℝ),
    Gen.Dat0 σ J T' bs ψ θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν ∧
    (∀ y : Fin d.m → E, SiegelWeilU.hE σ J y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    0 < C ∧ (∃ t : ℝ, ∀ z : ℂ, t < z.re →
      (Integrable (fun β => flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x)) lam →
        Integrable (Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (SiegelWeilU.inclR (AF F))) z) ν) ∧
      ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
        c * (C : ℂ) ^ (z - s0 d.m d.n) *
          ∫ b, Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (SiegelWeilU.inclR (AF F))) z b ∂ν) ∧
    ∃ μH 𝓕, SiegelWeilU.IsHaarH F E σ d.m J μH ∧ SiegelWeilU.IsFDH F E σ d.m J μH 𝓕 ∧
      d.orb T (d.om x Φ) = c * SiegelWeilU.meanC μH 𝓕
        (SiegelWeilU.thetaS F E σ d.m J Φg {X | SiegelWeilU.gramE σ J X = T'})

def CorePure_k (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ) : Prop := ForAllSD fun d => ∀ (R : RD_k d),
  ok d.m d.n → d.EisAll → ∀ Φ, d.KFin Φ → ∀ P gf, IsPureBy_k R Φ P gf →
    (vac → P = fun _ => 1) → ∀ x, IsLevi_k d x → WhitAtC_k c d Φ x

def CoreX_k : Prop := ∀ (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ),
  TAll_k → SiegelWeilDatumProperties → SecK_k → Unfold_k → Gen.WhitGenX ok vac c → GenDictX_k → CorePure_k ok vac c

def KFinK_k : Prop := ForAllSD fun d => ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ)

private theorem all_kfin_k (ok : ℕ → ℕ → Prop) (c : ℂ) (hI : IwaRedC_k) (hT : TAll_k) (hTC : ThetaCoef_k)
    (hLB : LamBd_k) (hR : RDEx_k) (hF : FockMem_k) (hK : KFinPoly_k) (hPK : PolyKFin_k) (hS : SecK_k) (hU : Unfold_k)
    (hP : PureSpan_k) (hL : LinRedC_k) (hC : CorePure_k ok False c) (hKK : KFinK_k)
    (d : SD_k σ) (hok : ok d.m d.n) (hE : d.EisAll) : ∀ Φ, d.KFin Φ → ∀ x, WhitAtC_k c d Φ x :=
  hI hT c F E σ d d.KFin (fun _ h => h.1) (hKK F E σ d) fun Φ hΦ x hx => by
    obtain ⟨R⟩ := hR F E σ d
    obtain ⟨k, cs, Φs, hs, rfl⟩ := hP hT hF hPK F E σ d R Φ hΦ (hK F E σ d R Φ hΦ)
    refine hL hT hTC hLB hU hS c F E σ d hE k cs Φs (fun i => (hs i).1) x fun i => ?_
    obtain ⟨P, gf, hpg⟩ := (hs i).2
    exact hC F E σ d R hok hE (Φs i) (hs i).1 P gf hpg False.elim x hx

theorem whitK_of_X_k (hI : IwaRedC_k) (hP : PureSpan_k) (hL : LinRedC_k) (hC : CoreX_k) (hD : GenDictX_k)
    (hKK : KFinK_k) (hT : TAll_k) (hA : SiegelWeilDatumProperties) (hR : RDEx_k) (hF : FockMem_k) (hK : KFinPoly_k)
    (hS : SecK_k) (hU : Unfold_k) (hW : Gen.WhitGenLt) (hTC : ThetaCoef_k) (hLB : LamBd_k) (hPK : PolyKFin_k) :
    WhitK_k :=
  fun F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hc ε w hw T hT' x => by
    simpa only [one_mul] using all_kfin_k (fun M n => n < M) 1 hI hT hTC hLB hR hF hK hPK hS hU hP hL
      (hC _ _ _ hT hA hS hU hW hD) hKK d hnm hE Φ hΦ x nb lam 𝓖 hc ε w hw T hT'

theorem whitEq_of_X_k (hI : IwaRedC_k) (hP : PureSpan_k) (hL : LinRedC_k) (hC : CoreX_k) (hD : GenDictX_k)
    (hKK : KFinK_k) (hT : TAll_k) (hA : SiegelWeilDatumProperties) (hR : RDEx_k) (hF : FockMem_k) (hK : KFinPoly_k)
    (hS : SecK_k) (hU : Unfold_k) (hEW : EisWk_k) (hW : Gen.WhitGenEq) (hTC : ThetaCoef_k) (hLB : LamBd_k)
    (hPK : PolyKFin_k) : WhitEq_k :=
  fun _ _ _ _ _ _ _ _ d hmn Φ hΦ nb lam 𝓖 hc ε w hw T hT' x =>
    all_kfin_k (fun M n => M = n ∧ 1 ≤ M) 2 hI hT hTC hLB hR hF hK hPK hS hU hP hL
      (hC _ _ _ hT hA hS hU hW hD) hKK d ⟨hmn, d.ok.hm⟩ (fun Φ' hΦ' => hEW _ _ _ d _ _ (hS _ _ _ d Φ' hΦ'))
      Φ hΦ x nb lam 𝓖 hc ε w hw T hT'

theorem whitLow_of_X_k (hI : IwaRedC_k) (hV : VacSpan_k) (hL : LinRedC_k) (hC : CoreX_k) (hD : GenDictX_k)
    (hVK : VacK_k) (hT : TAll_k) (hA : SiegelWeilDatumProperties) (hF : FockMem_k) (hS : SecK_k) (hU : Unfold_k)
    (hEW : EisWk_k) (hW : Gen.WhitGenLow) (hTC : ThetaCoef_k) (hLB : LamBd_k) (hPK : PolyKFin_k) : WhitLow_k := by
  intro F E _ _ _ _ _ σ d R hmn Φ hΦ hvac nb lam 𝓖 hc ε w hw T hT' x
  have hE : d.EisAll := fun Φ' hΦ' => hEW F E σ d _ _ (hS F E σ d Φ' hΦ')
  have hcore := hC _ _ _ hT hA hS hU hW hD
  refine hI hT 0 F E σ d (fun Φ => Φ ∈ d.sch ∧ d.T Φ ∈ R.vac) (fun _ h => h.1)
    (fun Φ h k hk => ⟨d.ok.dbl.weil.2.1.pres k Φ h.1, (hVK F E σ d R).1 Φ h.1 h.2 k hk⟩) ?_ Φ ⟨hΦ, hvac⟩
    x nb lam 𝓖 hc ε w hw T hT'
  intro Φ' h' x' hx'
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hV hT hF hPK hVK F E σ d R Φ' h'.1 h'.2
  refine hL hT hTC hLB hU hS 0 F E σ d hE k cs Φs (fun i => (hs i).1) x' fun i => ?_
  obtain ⟨gf, hpg⟩ := (hs i).2.2
  exact hcore F E σ d R ⟨hmn, d.ok.hm⟩ hE (Φs i) (hs i).1 _ gf hpg (fun _ => rfl) x' hx'

theorem meas_detA_k (d : SD_k σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact meas_det_of_hasSig (hA.sig w)
    · have h := meas_det_of_hasSig (hA.sig w); rw [Matrix.det_smul] at h; exact fun h0 => h (by rw [h0, mul_zero])
  intro h0; apply key; have hm := RingHom.map_det (d.B.emb w).1 d.A.J
  rw [RingHom.mapMatrix_apply, h0, map_zero] at hm; exact hm.symm

private theorem th_mem_iff_loc (d : SD_k σ) {η : E} (hη : η ≠ 0) (g : GL (Fin d.m) (AE F E)) :
    g ∈ UG (cA σ) (incM F d.A.J) ↔ g ∈ SiegelWeilU.HR (AF F) σ (Jd_k d η) := by
  have hc : IsUnit (inclR (F := F) (E := E) (AF F) η) := (Ne.isUnit hη).map _
  have hm : (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (SiegelWeilU.sigR (AF F) σ) =
      (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) := by ext i j; exact th_sigR_eq _
  have hJR : SiegelWeilU.JR (AF F) (Jd_k d η) = inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ := by
    ext i j; simp [SiegelWeilU.JR, Jd_k, incM, th_inclR_eq, Matrix.transpose_apply, map_mul]
  change (g : Matrix _ _ (AE F E))ᵀ * incM F d.A.J * (g : Matrix _ _ (AE F E)).map (cA σ) = incM F d.A.J ↔
    SiegelWeilU.cT (SiegelWeilU.sigR (AF F) σ) (g : Matrix _ _ (AE F E)) * SiegelWeilU.JR (AF F) (Jd_k d η) *
      (g : Matrix _ _ (AE F E)) = SiegelWeilU.JR (AF F) (Jd_k d η)
  rw [hJR, SiegelWeilU.cT, hm]
  set L := (g : Matrix _ _ (AE F E))ᵀ * incM F d.A.J * (g : Matrix _ _ (AE F E)).map (cA σ)
  have hL : ((g : Matrix _ _ (AE F E)).map (cA σ))ᵀ * (inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ) *
      (g : Matrix _ _ (AE F E)) = inclR (F := F) (E := E) (AF F) η • Lᵀ := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hL]; refine ⟨fun h => by rw [h], fun h => ?_⟩
  have h2 := congrArg (fun M => (hc.unit⁻¹ : (AE F E)ˣ) • M) h
  simp only [Units.smul_def, smul_smul, hc.val_inv_mul, one_smul] at h2; simpa using congrArg Matrix.transpose h2

theorem thetaDict_k : ThetaDict_k := by
  intro F E _ _ _ _ _ σ d η hη _
  let thE : UA σ d.A.J ≃* SiegelWeilU.HA (AF F) σ (Jd_k d η) :=
    MulEquiv.subgroupCongr (Subgroup.ext (th_mem_iff_loc d hη))
  have hc1 : Continuous thE := continuous_subtypeVal.subtype_mk _
  have hc2 : Continuous thE.symm := continuous_subtypeVal.subtype_mk _
  let thM : UA σ d.A.J ≃ᵐ SiegelWeilU.HA (AF F) σ (Jd_k d η) := (Homeomorph.mk thE.toEquiv hc1 hc2).toMeasurableEquiv
  let thE' : UA σ d.A.J → SiegelWeilU.HR (AF F) σ (Jd_k d η) := fun g => thE g
  have hrat : ∀ g : UA σ d.A.J, g ∈ ratU σ d.A.J ↔ thE' g ∈ SiegelWeilU.HFinIn (AF F) σ (Jd_k d η) := fun g => by
    rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range, SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf,
      SiegelWeilU.HFin, Subgroup.mem_map]
    refine ⟨?_, fun ⟨γ, _, hγ⟩ => ⟨γ, hγ⟩⟩
    rintro ⟨γ, hγ⟩; refine ⟨γ, ?_, hγ⟩
    have hg : (g.1 : GL (Fin d.m) (AE F E)) ∈ SiegelWeilU.HR (AF F) σ (Jd_k d η) := (th_mem_iff_loc d hη g.1).1 g.2
    rw [← hγ] at hg
    change SiegelWeilU.cT (σ : E →+* E) (γ : Matrix _ _ E) * Jd_k d η * (γ : Matrix _ _ E) = Jd_k d η
    apply Matrix.map_injective (th_inclR_injective (F := F) (E := E))
    change SiegelWeilU.cT (SiegelWeilU.sigR (AF F) σ) ((γ : Matrix _ _ E).map (inclR (F := F) (E := E) (AF F))) *
      SiegelWeilU.JR (AF F) (Jd_k d η) * (γ : Matrix _ _ E).map (inclR (F := F) (E := E) (AF F)) =
      SiegelWeilU.JR (AF F) (Jd_k d η) at hg
    dsimp only; rw [Matrix.map_mul, Matrix.map_mul, th_cT_map]; exact hg
  let thR : SiegelWeilU.HFinIn (AF F) σ (Jd_k d η) ≃ ratU σ d.A.J :=
    ⟨fun h => ⟨thE.symm h.1, (hrat _).2 (by
       rw [show thE' (thE.symm h.1) = h.1 from thE.apply_symm_apply h.1]; exact h.2)⟩,
     fun g => ⟨thE' g.1, (hrat _).1 g.2⟩, fun _ => Subtype.ext (thE.apply_symm_apply _),
     fun _ => Subtype.ext (thE.symm_apply_apply _)⟩
  have := d.ok.haar
  refine ⟨d.μ.map thM, thM '' d.D, th_haar_map d.μ thE hc1 hc2,
    d.ok.dom.image_of_equiv thM.toEquiv ⟨thM.symm.measurable.aemeasurable, by
      change Measure.map thM.symm (Measure.map thM d.μ) ≪ d.μ; rw [MeasurableEquiv.map_symm_map]⟩ thR (fun _ _ => rfl),
    fun T T₀ hT Φ _ => ?_⟩
  rw [SD_k.orb, setAverage_eq, SiegelWeilU.meanC, MeasurableEquiv.map_apply, thM.preimage_image, thM.restrict_map,
    thM.preimage_image, integral_map_equiv, measureReal_def]
  congr 1; refine integral_congr_ae (ae_of_all _ fun g => ?_); simp only [SiegelWeilU.thetaS]
  have hgram : ∀ X : d.ME,
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • incM F T₀ ↔ SiegelWeilU.gramE σ (Jd_k d η) Xᵀ = Td η T₀ := fun X => by
    have h1 : d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
      have hcA : (incM F X).map (cA σ) = incM F (X.map σ) := by ext i j; exact th_cA_incl _
      rw [SD_k.gram, hcA]; simp only [incM, Matrix.transpose_map, Matrix.map_mul]
    have h2 : SiegelWeilU.gramE σ (Jd_k d η) Xᵀ = η • (Xᵀ * d.A.J * X.map σ)ᵀ := by
      ext a b
      simp only [SiegelWeilU.gramE, SiegelWeilU.hE, SiegelWeilU.hform, Jd_k, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_coe, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hs : ((-2 : ℤ) • incM F T₀ : d.Mn) = incM F ((-2 : ℤ) • T₀) := by
      ext i j; simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul]
    rw [h1, h2, Td, hs]; refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [th_incM_injective h]; ext i j
      simp only [Matrix.smul_apply, Matrix.transpose_apply]; rw [zsmul_eq_mul, smul_eq_mul]; push_cast; ring
    · congr 1; ext i j; have := congrFun (congrFun h j) i
      simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at this
      simp only [Matrix.smul_apply, zsmul_eq_mul]; push_cast at this ⊢
      apply mul_left_cancel₀ hη; rw [this]; ring
  let e : {X : d.ME // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Fin d.n → Fin d.m → E | SiegelWeilU.gramE σ (Jd_k d η) X = Td η T₀} :=
    ⟨fun X => ⟨X.1ᵀ, (hgram X.1).1 (hT ▸ X.2)⟩,
     fun Y => ⟨Matrix.transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E), by rw [hT]; exact (hgram _).2 Y.2⟩,
     fun _ => Subtype.ext (Matrix.transpose_transpose _),
     fun Y => Subtype.ext (Matrix.transpose_transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E))⟩
  have hact (M : GL (Fin d.m) (AE F E)) (X : d.ME) :
      toMx (SiegelWeilU.actTup (AF F) M (SiegelWeilU.ratTup (AF F) Xᵀ)) =
        (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) * incM F X := by
    ext a j; simp only [toMx, SiegelWeilU.actTup, SiegelWeilU.ratTup, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, incM, Matrix.map_apply, Matrix.transpose_apply, th_inclR_eq]
  rw [← e.tsum_eq]; refine tsum_congr fun X => ?_
  simp only [e, Equiv.coe_fn_mk]; rw [hact]; rfl

theorem iwaRedC_k : IwaRedC_k := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x; obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := par_decomp_k d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) d.s₀ z (w * nb β * (n0 * m0 * k)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) =
      fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) d.s₀ z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := funext fun z => by
    erw [← int_n_k d nb lam 𝓖 hcd T w n0 m0 β₀ hn]; congr 1; funext β; unfold GlobalTheory.ThK.Dbl.flat
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc],
      a_mul_K_k d _ k hk, constantTerm_mul_right]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
    exact orb_n_k hT d T (om_mem_sch_k d _ (om_mem_sch_k d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _; rw [e1, e2, mul_left_comm]; exact holValueAt_const_mul _ key

theorem lin_psi_meas_k (d : SD_k σ) (M : d.Mn) : Measurable (fun β : d.nA_ => d.B.ψ (-d.tt (M * β.1))) := by
  rw [show (fun β : d.nA_ => d.B.ψ (-d.tt (M * β.1))) = fun β =>
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) from funext fun β => by
    simp only [SD_k.tt, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, ← Finset.sum_neg_distrib,
      lin_addChar_sum]]
  have : OpensMeasurableSpace (AE F E) := ⟨le_rfl⟩
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_
  exact (d.ok.good.std.1.comp (IsModuleTopology.continuous_of_linearMap
    ((Algebra.trace (AF F) (AE F E)).comp (LinearMap.mulLeft (AF F) (M i k)))).neg).measurable.comp
    ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_subtypeVal))
end PositivityTheory.SiegelWeilFormula.KWhit

namespace PositivityTheory.SiegelWeilFormula
open scoped Classical SchwartzMap
namespace KW
def insW_k (d : SD_k σ) (w : InfinitePlace F) (z : ℂ) : AE F E := Krd.sc_k d (Pi.single w z)
theorem insW_self_k (d : SD_k σ) (w : InfinitePlace F) (z : ℂ) : piInf (d.B.emb w) (insW_k d w z) = z := by
  rw [insW_k, Krd.sc_pi_k, Pi.single_eq_same]
theorem insW_ne_k (d : SD_k σ) (w : InfinitePlace F) {w' : InfinitePlace F} (hw : w' ≠ w) (z : ℂ) :
    piInf (d.B.emb w') (insW_k d w z) = 0 := by rw [insW_k, Krd.sc_pi_k, Pi.single_eq_of_ne hw]
theorem insW_fin_k (d : SD_k σ) (w : InfinitePlace F) (z : ℂ) : finOne F • insW_k d w z = 0 := Krd.sc_fin_k d _
private theorem insW_add_k (d : SD_k σ) (w : InfinitePlace F) (z z' : ℂ) :
    insW_k d w (z + z') = insW_k d w z + insW_k d w z' := by
  rw [insW_k, insW_k, insW_k, Pi.single_add, Krd.sc_k, (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.2.1]
def insL_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (v : Fin d.m → Fin d.n → ℂ) : d.MxE :=
  ((R.fr w).1 * (Matrix.of v).map star).map (insW_k d w)
def Supp_k {d : SD_k σ} (w : InfinitePlace F) (Z : d.MxE) : Prop :=
  (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0
section
variable {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F)
theorem cw_insL_k (v : Fin d.m → Fin d.n → ℂ) : d.cw w (insL_k R w v) = (R.fr w).1 * (Matrix.of v).map star := by
  ext _ _; simp only [SD_k.cw, insL_k, Matrix.map_apply, insW_self_k]
theorem insL_supp_k (v : Fin d.m → Fin d.n → ℂ) : Supp_k w (insL_k R w v) :=
  ⟨fun _ hw' => Matrix.ext fun _ _ => by simp only [SD_k.cw, insL_k, Matrix.map_apply, insW_ne_k d w hw',
    Matrix.zero_apply],
   Matrix.ext fun _ _ => by simp only [insL_k, Matrix.smul_apply, Matrix.map_apply, insW_fin_k, Matrix.zero_apply]⟩
theorem insL_add_k (v v' : Fin d.m → Fin d.n → ℂ) : insL_k R w (v + v') = insL_k R w v + insL_k R w v' := by
  have e : (R.fr w).1 * (Matrix.of (v + v')).map star =
      (R.fr w).1 * (Matrix.of v).map star + (R.fr w).1 * (Matrix.of v').map star := by
    rw [← Matrix.mul_add]; congr 1; ext _ _; simp
  unfold insL_k; rw [e]; ext _ _; simp only [Matrix.map_apply, Matrix.add_apply, insW_add_k]
theorem insL_zero_k : insL_k R w 0 = 0 := by
  have h := insL_add_k R w 0 0; rw [add_zero] at h
  calc insL_k R w 0 = insL_k R w 0 + insL_k R w 0 - insL_k R w 0 := by abel
    _ = 0 := by rw [← h, sub_self]
theorem rest_inv_k (X Z : d.MxE) (hZ : Supp_k w Z) :
    (X + Z) - insL_k R w (R.loc w (X + Z)) = X - insL_k R w (R.loc w X) := by
  have hloc : insL_k R w (R.loc w Z) = Z := Place.cw_ext_k d (fun w' => by
    by_cases hw : w' = w
    · subst w'; rw [cw_insL_k, ← cw_loc_k]
    · rw [(insL_supp_k R w _).1 w' hw, hZ.1 w' hw]) (by rw [(insL_supp_k R w _).2, hZ.2])
  have hadd : R.loc w (X + Z) = R.loc w X + R.loc w Z := by
    unfold RD_k.loc; rw [show d.cw w (X + Z) = d.cw w X + d.cw w Z from Matrix.map_add _ (map_add _) X Z,
      Matrix.mul_add]; exact Matrix.map_add _ star_add _ _
  rw [hadd, insL_add_k, hloc]; abel
end
theorem psi_add_right_k (d : SD_k σ) (ε : ℤˣ) (X Z Z' : d.MxE) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z + Z'))) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z')) := by
  rw [show d.gram X (Z + Z') = d.gram X Z + d.gram X Z' by
    unfold SD_k.gram; rw [Matrix.map_add _ (map_add _), Matrix.mul_add],
    SD_k.tt, SD_k.tt, SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem psi_add_left_k (d : SD_k σ) (ε : ℤˣ) (X X' Z : d.MxE) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (X + X') Z)) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X' Z)) := by
  rw [show d.gram (X + X') Z = d.gram X Z + d.gram X' Z by
    unfold SD_k.gram; rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul],
    SD_k.tt, SD_k.tt, SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem gram_supp_cmp_k (d : SD_k σ) (w : InfinitePlace F) {Z' Z : d.MxE}
    (hZ' : Supp_k w Z') (hZ : d.cw w Z = 0) : d.gram Z' Z = 0 := by
  refine Place.cw_ext_k d (fun w' => ?_)
    (by unfold SD_k.gram; rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hZ'.2]; simp)
  rw [cw_gram_k]
  by_cases hw : w' = w
  · subst hw; rw [hZ, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]; exact (Matrix.map_zero _ (map_zero _)).symm
  · rw [hZ'.1 w' hw, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
    exact (Matrix.map_zero _ (map_zero _)).symm
theorem psi_zero_gram_k (d : SD_k σ) (ε : ℤˣ) : d.B.ψ (((ε : ℤ) : AF F) * d.tt (0 : d.Mn)) = 1 := by simp [SD_k.tt]
theorem kernel_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (ε : ℤˣ) (X : d.MxE)
    (u : Fin d.m → Fin d.n → ℂ) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (insL_k R w u))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u)).re : ℂ)) := by
  set M := d.gram X (insL_k R w u)
  have hM1 (w') (hw : w' ≠ w) : d.cw w' M = 0 := by
    rw [cw_gram_k, (insL_supp_k R w u).1 w' hw, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
  have hM2 : finOne F • M = 0 := by
    show finOne F • (Xᵀ * incM F d.A.J * (insL_k R w u).map (cA σ)) = 0
    rw [← Matrix.mul_smul, show finOne F • (insL_k R w u).map (cA σ) = (finOne F • insL_k R w u).map (cA σ) by
      ext _ _; simp [map_smul], (insL_supp_k R w u).2]; simp
  have ptr (u') : piInf (d.B.emb u') M.trace = (d.cw u' M).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, SD_k.cw, Matrix.map_apply, map_sum]
  have hpsi : d.B.ψ (((ε : ℤ) : AF F) * d.tt M) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (((ε : ℤ) : ℂ) * (d.cw w M).trace).re : ℝ) : ℂ)) := by
    have hz : ((ε : ℤ) : AF F) * d.tt M = Algebra.trace (AF F) (AE F E) ((ε : ℤ) • M.trace) := by
      rw [map_zsmul, zsmul_eq_mul]; rfl
    rw [hz, Place.psi_trace_at d.std d.cm d.B.emb w _
      (by rw [smul_comm, ← Matrix.trace_smul, hM2, Matrix.trace_zero, smul_zero])
      (fun u' hu => by rw [map_zsmul, ptr, hM1 u' hu, Matrix.trace_zero, smul_zero]), map_zsmul, ptr, zsmul_eq_mul]
  have e1 : d.cw w M = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) := by
    rw [cw_gram_k, cw_loc_k R w X, cw_insL_k, Matrix.transpose_mul,
      show ((R.fr w).1 * (Matrix.of u).map star).map star = (R.fr w).1.map star * Matrix.of u by
        ext _ _; simp [Matrix.mul_apply]]
    calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of u)
        = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of u := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [frJ_k, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [hpsi, e1, Matrix.trace_smul, smul_eq_mul]; congr 1
  rw [show -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ * Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) =
      ((-2 : ℝ) : ℂ) * (((ε : ℤ) : ℂ) * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u))) by push_cast; ring, Complex.re_ofReal_mul]
  push_cast; ring
end KW

namespace KFock
def cmpW_k (d : SD_k σ) (w : InfinitePlace F) : AddSubgroup d.MxE where
  carrier := {X | d.cw w X = 0}
  zero_mem' := Matrix.map_zero _ (map_zero _)
  add_mem' {X Z} hX hZ := by
    show d.cw w (X + Z) = 0; rw [show d.cw w (X + Z) = d.cw w X + d.cw w Z from Matrix.map_add _ (map_add _) X Z]
    rw [show d.cw w X = 0 from hX, show d.cw w Z = 0 from hZ, add_zero]
  neg_mem' {X} hX := by
    show d.cw w (-X) = 0; rw [show d.cw w (-X) = -d.cw w X from Matrix.map_neg _ (map_neg _) X]
    exact neg_eq_zero.2 hX
private theorem loc_add'_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (X Z : d.MxE) :
    R.loc w (X + Z) = R.loc w X + R.loc w Z := by
  unfold RD_k.loc; rw [show d.cw w (X + Z) = d.cw w X + d.cw w Z from Matrix.map_add _ (map_add _) X Z, Matrix.mul_add]
  exact Matrix.map_add _ star_add _ _
theorem loc_of_mem_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) {b : d.MxE} (hb : b ∈ cmpW_k d w) :
    R.loc w b = 0 := by
  unfold RD_k.loc; rw [show d.cw w b = 0 from hb, Matrix.mul_zero]; exact Matrix.map_zero _ (star_zero _)
theorem intFact_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (ν : Measure d.MxE) (hν : d.IsCov ν) :
    ∃ (C : ℝ) (μ' : Measure (cmpW_k d w)), 0 < C ∧ μ'.IsAddHaarMeasure ∧
      ∀ (f : d.LF) (Ψ : d.MF), d.IsAwayW w Ψ → ∫ X, R.tens w f Ψ X ∂ν = C * (∫ u, f u) * ∫ Z, Ψ Z.1 ∂μ' := by
  have := hν.1; obtain ⟨_, _, _, _⟩ := KFock.mxTop_k d
  have : LocallyCompactSpace (cmpW_k d w) :=
    (isClosed_eq (Place.continuous_cw_k d w) continuous_const).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (cmpW_k d w) :=
    TopologicalSpace.Subtype.secondCountableTopology (cmpW_k d w : Set d.MxE)
  have : BorelSpace (cmpW_k d w) := Subtype.borelSpace _
  have := volume_isAddHaar d.m d.n
  have loc_sW (u) : R.loc w (KW.insL_k R w u) = u := by
    unfold RD_k.loc; rw [KW.cw_insL_k, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]; ext _ _; simp
  have hlocc : Continuous (R.loc w) :=
    (continuous_const.matrix_mul (Place.continuous_cw_k d w)).matrix_map continuous_star
  have hsW : Continuous (KW.insL_k R w) :=
    (continuous_const.matrix_mul (continuous_id.matrix_map continuous_star)).matrix_map
      ((Krd.sc_cont_k d).comp (continuous_pi fun w' => by
        by_cases h : w' = w
        · subst h; simp only [Pi.single_eq_same]; exact continuous_id
        · simp only [Pi.single_eq_of_ne h]; exact continuous_const))
  have mem (X : d.MxE) : X - KW.insL_k R w (R.loc w X) ∈ cmpW_k d w := by
    show d.cw w (X - KW.insL_k R w (R.loc w X)) = 0
    unfold SD_k.cw; rw [Matrix.map_sub _ (map_sub _) _ _, ← SD_k.cw, ← SD_k.cw, KW.cw_insL_k, ← KW.cw_loc_k, sub_self]
  let Φ : (Fin d.m → Fin d.n → ℂ) × cmpW_k d w ≃ₜ+ d.MxE :=
    { toFun p := KW.insL_k R w p.1 + p.2.1
      invFun X := (R.loc w X, ⟨X - KW.insL_k R w (R.loc w X), mem X⟩)
      left_inv := fun ⟨u, b, hb⟩ => by
        have e1 : R.loc w (KW.insL_k R w u + b) = u := by rw [loc_add'_k, loc_sW, loc_of_mem_k d R w hb, add_zero]
        refine Prod.ext e1 (Subtype.ext ?_)
        show KW.insL_k R w u + b - KW.insL_k R w (R.loc w _) = b; rw [e1, add_sub_cancel_left]
      right_inv X := add_sub_cancel _ _
      map_add' p q := by show KW.insL_k R w (p.1 + q.1) + (p.2.1 + q.2.1) = _; rw [KW.insL_add_k]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtypeVal.comp continuous_snd)
      continuous_invFun := hlocc.prodMk ((continuous_id.sub (hsW.comp hlocc)).subtype_mk _) }
  obtain ⟨C, hC, hg⟩ := integral_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ))
    (Measure.addHaar : Measure (cmpW_k d w)) Φ
  refine ⟨C, Measure.addHaar, hC, inferInstance, fun f Ψ hΨ => ?_⟩
  rw [hg, show (fun p : (Fin d.m → Fin d.n → ℂ) × cmpW_k d w => R.tens w f Ψ (Φ p)) = fun p => f p.1 * Ψ p.2.1 from
    funext fun p => by
      show f (R.loc w (KW.insL_k R w p.1 + p.2.1)) * Ψ (KW.insL_k R w p.1 + p.2.1) = f p.1 * Ψ p.2.1
      rw [loc_add'_k, loc_sW, loc_of_mem_k d R w p.2.2, add_zero, add_comm,
        hΨ p.2.1 _ (KW.insL_supp_k R w p.1).1 (KW.insL_supp_k R w p.1).2],
    integral_prod_mul (μ := (volume : Measure (Fin d.m → Fin d.n → ℂ)))
      (ν := (Measure.addHaar : Measure (cmpW_k d w))) f (fun Z : cmpW_k d w => Ψ Z.1), mul_assoc]
end KFock
theorem SD_k.chiW_form (d : SD_k σ) (w : InfinitePlace F) :
    ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → d.chiW w z = (z / (‖z‖ : ℂ)) ^ k :=
  _root_.GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow (d.chiW w) (d.chiW_mul w) (d.chiW_cont w)
    (fun z _ => by by_cases h : IsUnit (d.uW w z) <;> simp [SD_k.chiW, h]) (d.chiW_pos w)
namespace RD_k
variable {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F)
def StepOK (x : d.G) (A : d.LF → d.LF) (B : d.MF → d.MF) : Prop :=
  (∀ f, IsSw f → IsSw (A f)) ∧ ∀ Ψ, d.IsAwayW w Ψ → d.IsAwayW w (B Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w (A f) (B Ψ)
def Good (y : GR d.n) (g f : d.LF) : Prop :=
  ∀ Ψ, d.IsAwayW w Ψ → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w g Ψ
def OkY (y : GR d.n) : Prop := ∀ f, IsSw f → ∃ g, IsSw g ∧ R.Good w y g f
def Lc (y : GR d.n) (f : d.LF) : d.LF := if h : ∃ g, IsSw g ∧ R.Good w y g f then h.choose else 0
theorem isLocOp_of_ok (h : ∀ y, R.OkY w y) : R.IsLocOp w (R.Lc w) := fun y f hf => by
  have hx := h y f hf; rw [show R.Lc w y f = hx.choose by simp only [Lc, dite_eq_left hx]]
  exact ⟨hx.choose_spec.1, fun Ψ hΨ Φ hΦ hT => hx.choose_spec.2 Ψ hΨ Φ hΦ hT⟩
theorem ok_of_step {y : GR d.n} {A : d.LF → d.LF} (h : R.StepOK w (R.ι w y) A id) : R.OkY w y := fun f hf =>
  ⟨A f, h.1 f hf, fun Ψ hΨ Φ hΦ hT => (h.2 Ψ hΨ).2 f hf Φ hΦ hT⟩
theorem step_comp (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {x x' : d.G} {A A' : d.LF → d.LF}
    {B B' : d.MF → d.MF} (h : R.StepOK w x A B) (h' : R.StepOK w x' A' B') :
    R.StepOK w (x * x') (A ∘ A') (B ∘ B') :=
  ⟨fun f hf => h.1 _ (h'.1 f hf), fun Ψ hΨ => ⟨(h.2 _ (h'.2 Ψ hΨ).1).1, fun f hf Φ hΦ hT => by
    rw [map_mul, mul_apply_eq_comp]
    exact (h.2 _ (h'.2 Ψ hΨ).1).2 _ (h'.1 f hf) _ (hsch x' Φ hΦ) ((h'.2 Ψ hΨ).2 f hf Φ hΦ hT)⟩⟩
theorem ok_mul (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {y y' : GR d.n} (h : R.OkY w y) (h' : R.OkY w y') :
    R.OkY w (y * y') := fun f hf => by
  obtain ⟨g', hg', hG'⟩ := h' f hf; obtain ⟨g, hg, hG⟩ := h g' hg'
  exact ⟨g, hg, fun Ψ hΨ Φ hΦ hT => by
    rw [map_mul, map_mul, mul_apply_eq_comp]; exact hG Ψ hΨ _ (hsch _ Φ hΦ) (hG' Ψ hΨ Φ hΦ hT)⟩
theorem loc_surj (X : d.MxE) (u : Fin d.m → Fin d.n → ℂ) : ∃ Z : d.MxE,
    (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0 ∧ R.loc w (X + Z) = u := by
  set M : Matrix (Fin d.m) (Fin d.n) ℂ := (R.fr w).1 * (Matrix.of u).map star - d.cw w X with hM
  refine ⟨M.map (KW.insW_k d w),
    fun w' hw' => Matrix.ext fun _ _ => by simp only [SD_k.cw, Matrix.map_apply, KW.insW_ne_k d w hw',
      Matrix.zero_apply],
    Matrix.ext fun _ _ => by simp only [Matrix.smul_apply, Matrix.map_apply, KW.insW_fin_k, Matrix.zero_apply], ?_⟩
  have hc : d.cw w (X + M.map (KW.insW_k d w)) = (R.fr w).1 * (Matrix.of u).map star := by
    have : d.cw w (M.map (KW.insW_k d w)) = M :=
      Matrix.ext fun _ _ => by simp only [SD_k.cw, Matrix.map_apply, KW.insW_self_k]
    rw [show d.cw w (X + M.map (KW.insW_k d w)) = d.cw w X + d.cw w (M.map (KW.insW_k d w)) from
      Matrix.map_add _ (map_add _) _ _, this, hM]; abel
  simp only [RD_k.loc, hc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]; ext _ _; simp
end RD_k
end PositivityTheory.SiegelWeilFormula
end
