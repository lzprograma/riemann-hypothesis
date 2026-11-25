module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ColEApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.EmEqInr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IdentityOnLastEmbedding
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaEps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaLine
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ParabolicThetaScalar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SubMulRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero

/-! # SiegelWeilMeasdictToMx: Consolidated global theta-kernel definitions and proofs (SiegelWeilMeasdictToMx). -/
@[expose] public section

noncomputable section

section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open Matrix (GeneralLinearGroup det_fromBlocks_zero₂₁ det_mul det_one fromBlocks fromBlocks_multiply
  isUnit_iff_isUnit_det of_apply submatrix_apply transpose_apply)
open Finset (sum_eq_single sum_eq_zero)
open Set (mem_singleton_iff)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace PositivityTheory.SiegelWeilFormula
namespace MeasD
open KWhit kfour
theorem meas_toMx_k (d : SD_k σ) (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (𝓕 : Set (Fin d.n → Fin d.m →
    AF F ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (MeasP.ratTupA F E d.n d.m) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ (μ.map toMx).IsAddHaarMeasure ∧
      IsAddFundamentalDomain d.ratM (toMx '' 𝓕) (μ.map toMx) ∧ μ.map toMx (toMx '' 𝓕) = 1 := by
  have hemb : MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) := (colM d.m d.n).measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact (colE d.m d.n).toAddEquiv.isAddHaarMeasure_map μ (colE d.m d.n).continuous
      (colE d.m d.n).symm.continuous
  · rw [kfour.ratM_eq_k]
    refine hF.image_of_equiv (colM d.m d.n).toEquiv ?_ (ratEq d.m d.n) ?_
    · exact ((colM d.m d.n).measurePreserving_symm μ).quasiMeasurePreserving
    · intro g x
      rfl
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective]; exact h1
end MeasD
namespace Avac
theorem inFrame_one_k (d : SD_k σ) : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, KWhit.incM_inv_mul_k]
theorem quasiCharacter_conj_embed {d : SD_k σ} (L : LD_k d) (g : L.sd.G) : IdentityOnLastRowsCols L.i₀ (inFrame d.b
                        (L.j g)) := fun u hu v => L.j_out g u hu v
theorem q_conj'_k {d : SD_k σ} (L : LD_k d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam)
    (g : L.sd.G) :
    IsQ F E L.i₀ (inFrame d.b (L.j g * q * (L.j g)⁻¹)) lam := by
  have hH : inFrame d.b (L.j g) * inFrame d.b (L.j g)⁻¹ = 1 := by
    rw [← KWhit.inFrame_mul_k, mul_inv_cancel, inFrame_one_k]
  rw [KWhit.inFrame_mul_k, KWhit.inFrame_mul_k]
  refine isQ_conj hq hH (quasiCharacter_conj_embed L g) ?_
  rw [← map_inv]
  exact quasiCharacter_conj_embed L g⁻¹
theorem par_frame_k (d : SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ (n0 m0 : d.G) (A D : d.Gn),
      inFrame d.b n0 = fromBlocks 1 ((inFrame d.b p).toBlocks₁₂ * (inFrame d.b p).toBlocks₂₂⁻¹) 0 1 ∧
      inFrame d.b m0 = fromBlocks A.1 0 0 D.1 ∧ A.1 = (inFrame d.b p).toBlocks₁₁ ∧
      D.1 = (inFrame d.b p).toBlocks₂₂ ∧ p = n0 * m0 := by
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, KWhit.incM_mul_inv_k d, det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, KWhit.incM_inv_mul_k d, det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : d.Mn2 := fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (isUnit_iff_isUnit_det _).2 (by rw [hMd_def, det_fromBlocks_zero₂₁]; exact hdet)
  obtain ⟨C', hC'⟩ := KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := KWhit.form_conj_in (cA σ).toRingHom (KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := KWhit.block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL d.N2 (AE F E) := hM0u.unit
  have hu := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : d.Mn2)ᵀ * dbl (incM F d.Y.J) *
      (u : d.Mn2).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : d.Mn2) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (isUnit_iff_isUnit_det A).2 hA
  have hDu := (isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, hAu.unit, hDu.unit, ?_, ?_, IsUnit.unit_spec hAu, IsUnit.unit_spec hDu,
    (inv_mul_cancel_right p m0).symm⟩
  · have e := KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
theorem q_T'_k (hT : TAll_k) {d : SD_k σ} (i₀ : Fin d.n) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E i₀
                        (inFrame d.b q) lam) :
    ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : d.MxE, (∀ a, X a i₀ = 0) → d.T (d.om q Φ) X = c * d.T Φ X := by
  set M := inFrame d.b q with hM
  obtain ⟨n0, m0, A, D, hn, hm, hA, hD, hp⟩ := par_frame_k d q (isQ_21 hq)
  refine ⟨(d.χ (GeneralLinearGroup.det A) : ℂ) *
    (((absE F E (GeneralLinearGroup.det A) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ), fun Φ hΦ X hX => ?_⟩
  have hD1 : ∀ j k, k ≠ i₀ → D.1 j k = (1 : d.Mn) j k := by
    rw [hD]; exact isQ_22 hq
  have hDu : IsUnit M.toBlocks₂₂.det := by
    rw [← hD]; exact (isUnit_iff_isUnit_det _).1 D.isUnit
  have hDi : ∀ j k, k ≠ i₀ → M.toBlocks₂₂⁻¹ j k = (1 : d.Mn) j k :=
    inv_col (isQ_22 hq) (Matrix.nonsing_inv_mul _ hDu)
  have hβ : ∀ i j, i ≠ i₀ → j ≠ i₀ → (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) i j = 0 := by
    intro i j hi hj
    rw [Matrix.mul_apply]
    refine sum_eq_zero fun k _ => ?_
    by_cases hk : k = i₀
    · subst hk; rw [hDi _ _ hj, Matrix.one_apply_ne (Ne.symm hj), mul_zero]
    · rw [isQ_12 hq i k hi hk, zero_mul]
  have hG : ∀ i j, (i = i₀ ∨ j = i₀) → d.gram X X i j = 0 := by
    intro i j hij
    simp only [SD_k.gram, Matrix.mul_apply, transpose_apply, Matrix.map_apply]
    refine sum_eq_zero fun b _ => ?_
    rcases hij with rfl | rfl
    · rw [Finset.sum_mul]
      refine sum_eq_zero fun a _ => ?_
      rw [hX a, zero_mul, zero_mul]
    · rw [hX b, map_zero, mul_zero]
  have htt : d.tt ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
    have : Matrix.trace ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
      simp only [Matrix.trace, Matrix.diag]
      refine sum_eq_zero fun i _ => ?_
      rw [Matrix.mul_apply]
      refine sum_eq_zero fun j _ => ?_
      by_cases h : i = i₀ ∨ j = i₀
      · rw [hG j i (h.symm), mul_zero]
      · push Not at h
        rw [hβ i j h.1 h.2, zero_mul]
    simp only [SD_k.tt, this, map_zero]
  have hXD : X * (D⁻¹).1ᵀ = X := by
    have h1 : X * D.1ᵀ = X := by
      ext a j
      rw [Matrix.mul_apply, sum_eq_single j]
      · rw [transpose_apply]
        by_cases hj : j = i₀
        · subst hj; rw [hX a, zero_mul]
        · rw [hD1 j j hj, Matrix.one_apply_eq, mul_one]
      · intro k _ hk
        rw [transpose_apply]
        by_cases hk0 : k = i₀
        · subst hk0; rw [hX a, zero_mul]
        · rw [hD1 j k hk0, Matrix.one_apply_ne (Ne.symm hk), mul_zero]
      · simp
    calc X * (D⁻¹).1ᵀ = X * D.1ᵀ * (D⁻¹).1ᵀ := by rw [h1]
      _ = X * ((D⁻¹).1 * D.1)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = X := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  have hm0s := KWhit.om_mem_sch_k d m0 hΦ
  rw [hp, map_mul, mul_apply_eq_comp, (hT.2.1 F E σ d _ hm0s).1 n0 _ hn X, htt, mul_zero, neg_zero,
    AddChar.map_zero_eq_one, one_mul, (hT.2.1 F E σ d Φ hΦ).2.1 m0 A D hm X, hXD]
section
variable (d : SD_k σ)
theorem isPar_of_frame_k (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ t : d.Gn, IsPar p t ∧ (GeneralLinearGroup.det t : AE F E) =
        (inFrame d.b p).toBlocks₁₁.det := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  set M := inFrame d.b p with hM
  let E1 : Matrix d.N2 (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix d.N2 (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) E) * tb.1 := htb
  have hcol : ∀ N : d.Mn2, N * E1 = N.toCols₁ := by
    intro N
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite]
  have hb := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hTb' : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul', Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have hME : M * E1 = E1 * M.toBlocks₁₁ := by
    rw [hcol]
    ext i j
    cases i with
    | inl i => simp [E1, Matrix.toCols₁, Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.one_apply]
    | inr i =>
      have := congrFun (congrFun h21 i) j
      simp only [Matrix.toBlocks₂₁, of_apply, Matrix.zero_apply] at this
      simp [E1, Matrix.toCols₁, this, Matrix.mul_apply]
  have hBm : IsUnit (incM F d.b.1) := (isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, KWhit.incM_mul_inv_k d, det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, KWhit.incM_inv_mul_k d, det_one]⟩)
  have hug := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hgb : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
    rw [← det_fromBlocks_zero₂₁ M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂, ← hgb]
    exact (isUnit_iff_isUnit_det M).1 hug
  have hA := isUnit_of_mul_isUnit_left hdet
  have hTbu : IsUnit (incM F tb.1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, hTb, det_one]⟩
  have hTbiu : IsUnit (incM F (tb⁻¹).1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, hTb', det_one]⟩
  have hu : IsUnit (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1) := by
    rw [isUnit_iff_isUnit_det, det_mul, det_mul]
    exact (hTbu.mul hA).mul hTbiu
  refine ⟨hu.unit, ?_, ?_⟩
  · show mat2 p * DC = DC * (hu.unit : d.Mn)
    rw [IsUnit.unit_spec, KWhit.matrixRep_eq_frameConj_inFrame d p]
    change incM F d.b.1 * M * incM F (d.b⁻¹).1 * DC = DC * (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1)
    rw [hdc]
    calc incM F d.b.1 * M * incM F (d.b⁻¹).1 * (incM F d.b.1 * E1 * incM F (tb⁻¹).1)
        = incM F d.b.1 * M * (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * incM F (tb⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * (M * E1) * incM F (tb⁻¹).1 := by
          rw [KWhit.incM_inv_mul_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * E1 * (incM F (tb⁻¹).1 * incM F tb.1) * M.toBlocks₁₁ * incM F (tb⁻¹).1 := by
          rw [hME, hTb', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, det_mul, det_mul,
        mul_comm _ M.toBlocks₁₁.det,
      mul_assoc, ← det_mul, hTb, det_one, mul_one]
theorem a_mul_par_k {q : d.G} {t : d.Gn} (hq : IsPar q t) (y : d.G) :
    d.a (q * y) = (absE F E (GeneralLinearGroup.det t) : ℝ) * d.a y := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa y
  rw [← mul_assoc, d.ok.hgt.val _ _ (KSplitP.isPar_mul hq hp) k hk, d.ok.hgt.val p t' hp k hk, map_mul, map_mul,
    NNReal.coe_mul]
end
section
variable {d : SD_k σ}
def emEq_k (L : LD_k d) : Fin L.n ⊕ Unit ≃ Fin d.n :=
  Equiv.ofBijective (Sum.elim L.em fun _ => L.i₀) ⟨by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (L.inj h)
    · exact absurd h ((L.rng (L.em a)).2 ⟨a, rfl⟩)
    · exact absurd h.symm ((L.rng (L.em b)).2 ⟨b, rfl⟩)
    · rfl, fun i => by
    by_cases h : i = L.i₀
    · exact ⟨Sum.inr (), h.symm⟩
    · obtain ⟨a, ha⟩ := (L.rng i).1 h
      exact ⟨Sum.inl a, ha⟩⟩
theorem emEq_inl_k (L : LD_k d) (a : Fin L.n) : emEq_k L (Sum.inl a) = L.em a := rfl
theorem emEq_inr_k (L : LD_k d) (u : Unit) : emEq_k L (Sum.inr u) = L.i₀ := rfl
theorem det_emb_k (L : LD_k d) (N : d.Mn) (N' : Matrix (Fin L.n) (Fin L.n)
    (AE F E))
    (h0 : ∀ k, N L.i₀ k = (1 : d.Mn) L.i₀ k ∧
      N k L.i₀ = (1 : d.Mn) k L.i₀)
    (h1 : N.submatrix L.em L.em = N') : N.det = N'.det := by
  rw [← Matrix.det_submatrix_equiv_self (emEq_k L) N]
  have hne : ∀ a, L.em a ≠ L.i₀ := fun a => (L.rng (L.em a)).2 ⟨a, rfl⟩
  have : N.submatrix (emEq_k L) (emEq_k L) = fromBlocks N' 0 0 1 := by
    ext (a | a) (b | b)
    · rw [submatrix_apply, emEq_inl_k, emEq_inl_k, Matrix.fromBlocks_apply₁₁, ← h1, submatrix_apply]
    · rw [submatrix_apply, emEq_inl_k, emEq_inr_k, Matrix.fromBlocks_apply₁₂, (h0 (L.em a)).2,
        Matrix.one_apply_ne (hne a), Matrix.zero_apply]
    · rw [submatrix_apply, emEq_inl_k, emEq_inr_k, Matrix.fromBlocks_apply₂₁, (h0 (L.em b)).1,
        Matrix.one_apply_ne (hne b).symm, Matrix.zero_apply]
    · rw [submatrix_apply, emEq_inr_k, Matrix.fromBlocks_apply₂₂, (h0 L.i₀).1, Matrix.one_apply_eq,
        Matrix.one_apply_eq]
  rw [this, det_fromBlocks_zero₂₁, det_one, mul_one]
theorem emm_inj_k (L : LD_k d) : Function.Injective (Sum.map L.em L.em) := Sum.map_injective.2 ⟨L.inj,
    L.inj⟩
theorem emm_rng_k (L : LD_k d) : ∀ c, c ∉ I0 L.i₀ ↔ c ∈ Set.range (Sum.map L.em L.em) := by
  rintro (c | c)
  · simp only [I0, Set.mem_insert_iff, mem_singleton_iff, Sum.inl.injEq, reduceCtorEq, or_false]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · exact ⟨a, Sum.inl_injective h⟩
      · simp at h
  · simp only [I0, Set.mem_insert_iff, mem_singleton_iff, Sum.inr.injEq, reduceCtorEq, false_or]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · simp at h
      · exact ⟨a, Sum.inr_injective h⟩
theorem idI_j_k (L : LD_k d) (g : L.sd.G) : IdI (I0 L.i₀) (inFrame d.b (L.j g)) := fun u hu v =>
    L.j_out g u hu v
theorem j_K_k (L : LD_k d) {k : L.sd.G} (hk : k ∈ L.sd.K) : L.j k ∈ d.K := by
  have hL := (L.ok.stdK k).1 hk
  refine (d.ok.stdK (L.j k)).2 ⟨fun w => ?_, fun k'' hk'' i j => ?_⟩
  · have hI := (idI_j_k L k).map (piInf (d.B.emb w))
    refine (hI.mul hI.ct).eq_one (emm_inj_k L) (emm_rng_k L) ?_
    rw [hI.sub_mul _ (emm_inj_k L) (emm_rng_k L), ← Matrix.conjTranspose_submatrix, Matrix.submatrix_map, L.j_in]
    exact hL.1 w
  · obtain ⟨k₀, hk₀, rfl⟩ : ∃ k₀ ∈ ({k, k⁻¹} : Set L.sd.G), k'' = L.j k₀ := by
      rcases hk'' with rfl | rfl
      · exact ⟨k, Or.inl rfl, rfl⟩
      · exact ⟨k⁻¹, Or.inr rfl, (map_inv L.j k).symm⟩
    by_cases hi : i ∈ I0 L.i₀
    · rw [(idI_j_k L k₀ i hi j).1]; exact KSplitW.finOne_one_mem_k d i j
    by_cases hj : j ∈ I0 L.i₀
    · rw [(idI_j_k L k₀ j hj i).2]; exact KSplitW.finOne_one_mem_k d i j
    obtain ⟨a, rfl⟩ := (emm_rng_k L i).1 hi
    obtain ⟨b, rfl⟩ := (emm_rng_k L j).1 hj
    have e := congrFun (congrFun (L.j_in k₀) a) b
    rw [submatrix_apply] at e
    rw [e]
    exact hL.2 k₀ hk₀ a b
theorem a_j_k (L : LD_k d) (h : L.sd.G) : d.a (L.j h) = L.a h := by
  obtain ⟨p', t', hp', k', hk', rfl⟩ := L.ok.hgt.iwa h
  have h21L := KWhit.parabolic_lowerLeft_block_zero L.sd p' t' hp'
  obtain ⟨t₂, hp₂, hdet₂⟩ := isPar_of_frame_k L.sd p' h21L
  have hI := idI_j_k L p'
  have h21 : (inFrame d.b (L.j p')).toBlocks₂₁ = 0 := by
    ext a b
    simp only [Matrix.toBlocks₂₁, of_apply, Matrix.zero_apply]
    by_cases ha : Sum.inr a ∈ I0 L.i₀
    · rw [(hI _ ha _).1]; simp
    by_cases hb : Sum.inl b ∈ I0 L.i₀
    · rw [(hI _ hb _).2]; simp
    obtain ⟨a', ha'⟩ := (emm_rng_k L _).1 ha
    obtain ⟨b', hb'⟩ := (emm_rng_k L _).1 hb
    rcases a' with a' | a'
    · simp at ha'
    rcases b' with b' | b'
    · have e := congrFun (congrFun (L.j_in p') (Sum.inr a')) (Sum.inl b')
      simp only [submatrix_apply] at e
      rw [← ha', ← hb', e]
      have := congrFun (congrFun h21L a') b'
      simpa [Matrix.toBlocks₂₁] using this
    · simp at hb'
  obtain ⟨t₁, hp₁, hdet₁⟩ := isPar_of_frame_k d (L.j p') h21
  have hdet : GeneralLinearGroup.det t₁ = GeneralLinearGroup.det t₂ := by
    refine Units.ext ?_
    rw [hdet₁, hdet₂]
    refine det_emb_k L _ _ (fun k => ⟨?_, ?_⟩) ?_
    · simp only [Matrix.toBlocks₁₁, of_apply]
      rw [(hI _ (Or.inl rfl) _).1]; simp [Matrix.one_apply]
    · simp only [Matrix.toBlocks₁₁, of_apply]
      rw [(hI _ (Or.inl rfl) _).2]; simp [Matrix.one_apply]
    · ext a b
      have e := congrFun (congrFun (L.j_in p') (Sum.inl a)) (Sum.inl b)
      simpa [Matrix.toBlocks₁₁] using e
  rw [map_mul, d.ok.hgt.val _ _ hp₁ _ (j_K_k L hk'), L.ok.hgt.val _ _ hp₂ _ hk', hdet]
theorem q_ht'_k (L : LD_k d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam)
    (h : L.sd.G) :
    d.a (q * L.j h) = (absE F E lam : ℝ) * L.a h := by
  obtain ⟨t, hp, hdet⟩ := isPar_of_frame_k d q (isQ_21 hq)
  have e : GeneralLinearGroup.det t = lam :=
    Units.ext (by rw [hdet, det_row (isQ_11 hq).1, (isQ_11 hq).2])
  rw [a_mul_par_k d hp, e, a_j_k L h]
theorem eps_eq_k (L : LD_k d) : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1
    (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have s := KWhit.rel_sign_k d ε hε
  have s' := KWhit.rel_sign_k L.sd ε' hε'
  refine ⟨ε, hε, ?_⟩
  suffices e : ε' = ε by rw [← e]; exact hε'
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · rw [s.1 hY, s'.1 hY']
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · rw [s.2 hY, s'.2 hY']
end
theorem frame_formE_k (d : SD_k σ) (ε : ℤˣ)
    (h : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E) := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, h]
  ext (i | i) (j | j)
  · simp [incM, Jm]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm, map_intCast]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · simp [incM, Jm]
theorem sub_form_k {d : SD_k σ} (L : LD_k d) (c : AE F E →+* AE F E) (ε : AE F E)
    (M : d.Mn2)
    (hr : ∀ b, b ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) b = 0) :
    (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em))ᵀ * Jm L.n ε *
        (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em)).map c =
      (Mᵀ * Jm d.n ε * M.map c).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) := by
  ext x y
  rw [submatrix_apply, form_apply, form_apply]
  have hx : Sum.map L.em L.em x ≠ Sum.inr L.i₀ := by
    rcases x with x | x
    · simp
    · simpa using (L.rng (L.em x)).2 ⟨x, rfl⟩
  have hy : Sum.map L.em L.em y ≠ Sum.inr L.i₀ := by
    rcases y with y | y
    · simp
    · simpa using (L.rng (L.em y)).2 ⟨y, rfl⟩
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun k => rfl)
  have : k = L.i₀ := by by_contra h; exact hk ((L.rng k).1 h)
  subst this
  rw [hr _ hx, hr _ hy, map_zero]; ring
theorem sub_J_k {d : SD_k σ} (L : LD_k d) (ε : AE F E) :
    (Jm d.n ε).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = Jm L.n ε := by
  ext (i | i) (j | j) <;> simp [Jm, Matrix.one_apply, L.inj.eq_iff]
theorem mkG_k (d : SD_k σ) (ε : ℤˣ)
    (hf : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E))
    (N : d.Mn2)
    (hN : Nᵀ * Jm d.n ((ε : ℤ) : AE F E) * N.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E)) :
    ∃ g : d.G, inFrame d.b g = N := by
  set J := Jm d.n ((ε : ℤ) : AE F E) with hJdef
  have hNu : IsUnit N.det := by
    have e : Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J)) = 1 := by
      calc Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J))
          = (Nᵀ * J * N.map (cA σ).toRingHom) * (((ε : ℤ) : AE F E) • J) := by simp only [Matrix.mul_assoc]
        _ = J * (((ε : ℤ) : AE F E) • J) := by rw [hN]
        _ = 1 := Jm_sq d.n ε
    have := congrArg Matrix.det e
    rw [det_mul, Matrix.det_transpose, det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  have hBm : IsUnit (incM F d.b.1) := (isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, KWhit.incM_mul_inv_k d, det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← det_mul, KWhit.incM_inv_mul_k d, det_one]⟩)
  have hM0u : IsUnit (incM F d.b.1 * N * incM F (d.b⁻¹).1) :=
    (hBm.mul ((isUnit_iff_isUnit_det _).2 hNu)).mul hBi
  have hf' := hf
  rw [← hf'] at hN
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (KWhit.incM_mul_inv_k d) hN
  let u : GL d.N2 (AE F E) := hM0u.unit
  have hu := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : d.Mn2)ᵀ * dbl (incM F d.Y.J) *
      (u : d.Mn2).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  refine ⟨⟨u, hmem⟩, ?_⟩
  show incM F (d.b⁻¹).1 * (u : d.Mn2) * incM F d.b.1 = N
  rw [hu]
  simp only [← Matrix.mul_assoc, KWhit.incM_inv_mul_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, KWhit.incM_inv_mul_k d, Matrix.mul_one]
theorem q_split'_k {d : SD_k σ} (L : LD_k d) (ε : ℤˣ)
    (hd : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hL : L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (p : d.G) (lam : (AE F E)ˣ)
    (hp : ∀ a, inFrame d.b p a (Sum.inl L.i₀) = if a = Sum.inl L.i₀ then (lam : AE F E) else 0) :
    ∃ g : L.sd.G, IsQ F E L.i₀ (inFrame d.b (p * (L.j g)⁻¹)) lam := by
  set M := inFrame d.b p with hMdef
  have hfd := frame_formE_k d ε hd
  have hfL := frame_formE_k L.sd ε hL
  have hMform : Mᵀ * Jm d.n ((ε : ℤ) : AE F E) * M.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E) := by
    have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
    have := KWhit.form_conj_in (cA σ).toRingHom (KWhit.incM_mul_inv_k d) hP
    have hfd' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
        Jm d.n ((ε : ℤ) : AE F E) := hfd
    rw [hfd'] at this
    exact this
  have hrow := row_zero (cA σ).toRingHom ε hMform hp
  have hsub := sub_form_k L (cA σ).toRingHom (((ε : ℤ) : AE F E)) M hrow
  rw [hMform, sub_J_k] at hsub
  obtain ⟨g, hg⟩ := mkG_k L.sd ε hfL _ hsub
  refine ⟨g, ?_⟩
  rw [KWhit.inFrame_mul_k, ← map_inv]
  set H' := inFrame d.b (L.j g⁻¹) with hH'
  have hI : IdI (I0 L.i₀) H' := idI_j_k L g⁻¹
  have hsubH : H'.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = inFrame L.b g⁻¹ := L.j_in g⁻¹
  have hinv : M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) * inFrame L.b g⁻¹ = 1 := by
    have e := KWhit.inFrame_mul_k L.sd g g⁻¹
    rw [mul_inv_cancel, inFrame_one_k] at e
    rw [← hg]; exact e.symm
  refine ⟨fun a b ha hb => ?_, fun a => ?_, fun b hb => ?_⟩
  · obtain ⟨a', rfl⟩ := (emm_rng_k L a).1 ha
    obtain ⟨b', rfl⟩ := (emm_rng_k L b).1 hb
    have e := congrFun (congrFun (hI.sub_mul_right M (emm_inj_k L) (emm_rng_k L)) a') b'
    rw [submatrix_apply, hsubH, hinv] at e
    rw [e]
    by_cases hab : a' = b'
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne ((emm_inj_k L).ne hab)]
  · rw [mul_col_one (fun v => (hI _ (Or.inl rfl) v).2)]
    exact hp a
  · rw [Matrix.mul_apply, sum_eq_single (Sum.inr L.i₀)]
    · rw [(hI _ (Or.inr rfl) b).1, Matrix.one_apply_ne (Ne.symm hb), mul_zero]
    · intro c _ hc
      rw [show inFrame d.b p (Sum.inr L.i₀) c = 0 from hrow c hc, zero_mul]
    · simp
namespace LineFix
theorem good_k (d : SD_k σ) : (PositivityTheory.RgEis.adCM σ d.χ).Good :=
  PositivityTheory.RgEis.Hd.cmGood_of PositivityTheory.RgEis.Hd.stdGood PositivityTheory.RgEis.Hd.dict
      PositivityTheory.RgEis.Hd.dictInf F E σ d.χ d.m
    d.ok.good.cm d.ok.good.unram d.ok.hecke d.ok.res
theorem cc_k (d : SD_k σ) (x : AE F E) : cA σ (cA σ x) = x := (good_k d).σσ x
theorem frame_eps_k (d : SD_k σ) : ∃ ε : ℤˣ, (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
    fromBlocks 0 1 (((ε : ℤ) : AE F E) • (1 : d.Mn)) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame; exact ⟨ε, frame_formE_k d ε hε⟩
variable {n : ℕ}
variable (d : SD_k σ)
theorem mL_mem_k (κ : d.Gn) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J) := by
  obtain ⟨ε, hε⟩ := frame_eps_k d
  have hN := Nk_form (σ := σ) (cc_k d) ((ε : ℤ) : AE F E) κ
  rw [← hε] at hN
  exact KWhit.form_conj_out (cA σ).toRingHom (KWhit.incM_mul_inv_k d) hN
theorem mL_mul_k (κ : d.Gn) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * (incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1) = 1 := by
  calc _ = incM F d.b.1 * Nk (σ := σ) κ * (incM F (d.b⁻¹).1 * incM F d.b.1) * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [KWhit.incM_inv_mul_k d, Matrix.mul_one, Matrix.mul_assoc (incM F d.b.1), Nk_mul_inv, Matrix.mul_one,
          KWhit.incM_mul_inv_k d]
def mL_k (κ : d.Gn) : d.G :=
  ⟨⟨incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1, incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1, mL_mul_k d κ,
    by simpa using mL_mul_k d κ⁻¹⟩, by
    show (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J)
    exact mL_mem_k d κ⟩
theorem inFrame_mL_k (κ : d.Gn) : inFrame d.b (mL_k d κ) = Nk (σ := σ) κ := by
  show incM F (d.b⁻¹).1 * (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * incM F d.b.1 = Nk (σ := σ) κ
  simp only [← Matrix.mul_assoc, KWhit.incM_inv_mul_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, KWhit.incM_inv_mul_k d, Matrix.mul_one]
theorem mL_inv_k (κ : d.Gn) : mL_k d κ⁻¹ = (mL_k d κ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  apply KWhit.inFrame_injective_k d
  rw [KWhit.inFrame_mul_k, inFrame_mL_k, inFrame_mL_k, Nk_mul_inv, inFrame_one_k]
theorem O_int_k {z : AE F E} (hz : z ∈ (PositivityTheory.RgEis.adCM σ d.χ).O) : finOne F • z ∈ intHat F E :=
  ((PositivityTheory.RgEis.Hd.dict F E).2.2.2.1 z).1 hz
theorem Nk_int_k {κ : d.Gn} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n))
                   (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • Nk (σ := σ) κ i j ∈ intHat F E := by
  have hκ' := hκ.1
  rcases i with i | i <;> rcases j with j | j
  · exact O_int_k d (hκ' i j).1
  · simp [Nk, (intHat F E).zero_mem]
  · simp [Nk, (intHat F E).zero_mem]
  · exact O_int_k d ((good_k d).σO _ (hκ' j i).2)
theorem Nk_unit_k {κ : d.Gn} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n))
                    (w : InfinitePlace F) :
    (Nk (σ := σ) κ).map (piInf (d.B.emb w)) * ((Nk (σ := σ) κ).map (piInf (d.B.emb w)))ᴴ = 1 := by
  obtain ⟨w', hw'⟩ := ((PositivityTheory.RgEis.Hd.dictInf F E σ d.ok.good.cm).2 d.B.emb).1 w
  set g := (PositivityTheory.RgEis.adCM σ d.χ).φ w' with hg
  have hU : (κ : d.Mn).map g ∈ Matrix.unitaryGroup (Fin d.n) ℂ := hκ.2 w'
  have hV : ((κ⁻¹ : d.Gn) : d.Mn).map g ∈
      Matrix.unitaryGroup (Fin d.n) ℂ := (inv_mem hκ).2 w'
  have hσφ : ∀ z, g (cA σ z) = (starRingEnd ℂ) (g z) := fun z => (good_k d).σφ w' z
  rcases hw' with hf | hf
  · have hf' : ∀ z, piInf (d.B.emb w) z = g z := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = fromBlocks ((κ : Matrix (Fin d.n) (Fin d.n)
        (AE F E)).map g) 0 0
        (star (((κ⁻¹ : d.Gn) : d.Mn).map g)) := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit hU (Unitary.star_mem hV)
  · have hf' : ∀ z, piInf (d.B.emb w) z = (starRingEnd ℂ) (g z) := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = fromBlocks (star ((κ : Matrix (Fin d.n) (Fin d.n)
        (AE F E)).map g))ᵀ 0 0
        ((((κ⁻¹ : d.Gn) : d.Mn).map g))ᵀ := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit (_root_.GlobalTheory.CompanionTheory.CMMirror.transpose_mem_unitary (Unitary.star_mem hU))
        (_root_.GlobalTheory.CompanionTheory.CMMirror.transpose_mem_unitary hV)
theorem mL_mem_K_k {κ : d.Gn} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL
                     (Fin d.n)) : mL_k d κ ∈ d.K := by
  refine (d.ok.stdK _).2 ⟨fun w => ?_, fun k' hk' i j => ?_⟩
  · rw [inFrame_mL_k]; exact Nk_unit_k d hκ w
  · rcases hk' with rfl | hk'
    · rw [inFrame_mL_k]; exact Nk_int_k d hκ i j
    · rw [mem_singleton_iff] at hk'
      subst hk'
      rw [← mL_inv_k, inFrame_mL_k]
      exact Nk_int_k d (inv_mem hκ) i j
end LineFix
theorem line_fix'_k {d : SD_k σ} (i₀ : Fin d.n) (x : d.G) : ∃ (p k : d.G) (lam : (AE F E)ˣ), k ∈ d.K ∧ x = p * k ∧
    ∀ a, inFrame d.b p a (Sum.inl i₀) = if a = Sum.inl i₀ then (lam : AE F E) else 0 := by
  obtain ⟨p0, t, hp, k1, hk1, rfl⟩ := d.ok.hgt.iwa x
  have h21 := KWhit.parabolic_lowerLeft_block_zero d p0 t hp
  obtain ⟨-, -, A, -, -, -, hA, -, -⟩ := par_frame_k d p0 h21
  obtain ⟨a1, ha1, κ, hκ, hAe⟩ := (LineFix.good_k d).iwa (Fin d.n) {i₀} A
  have hs : ∀ r, r ≠ i₀ → (a1 : d.Mn) r i₀ = 0 ∧
      ((a1⁻¹ : d.Gn) : d.Mn) r i₀ = 0 :=
    fun r hr => ha1 r (by simpa using hr) i₀ rfl
  have hunit : (a1 : d.Mn) i₀ i₀ *
      ((a1⁻¹ : d.Gn) : d.Mn) i₀ i₀ = 1 := by
    have := congrFun (congrFun (LineFix.val_mul_inv a1) i₀) i₀
    rw [Matrix.mul_apply, sum_eq_single i₀ (fun r _ hr => by rw [(hs r hr).2, mul_zero]) (by simp),
      Matrix.one_apply_eq] at this
    exact this
  refine ⟨p0 * (LineFix.mL_k d κ)⁻¹, LineFix.mL_k d κ * k1, Units.mkOfMulEqOne _ _ hunit,
    d.K.mul_mem (LineFix.mL_mem_K_k d hκ) hk1, by group, fun a => ?_⟩
  have hMb : inFrame d.b p0 = fromBlocks (A : d.Mn) (inFrame d.b p0).toBlocks₁₂ 0
      (inFrame d.b p0).toBlocks₂₂ := by
    rw [hA, ← h21, Matrix.fromBlocks_toBlocks]
  have hAk : (A : d.Mn) * ((κ⁻¹ : d.Gn) : Matrix (Fin d.n) (Fin d.n)
      (AE F E)) =
      a1 := by
    rw [hAe, Units.val_mul, Matrix.mul_assoc, LineFix.val_mul_inv, Matrix.mul_one]
  rw [KWhit.inFrame_mul_k, ← LineFix.mL_inv_k, LineFix.inFrame_mL_k, hMb]
  rcases a with r | r
  · simp only [LineFix.Nk, fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.fromBlocks_apply₁₁, hAk]
    by_cases hr : r = i₀
    · subst hr; simp
    · rw [(hs r hr).1]; simp [hr]
  · simp [LineFix.Nk, fromBlocks_multiply]
end Avac
end PositivityTheory.SiegelWeilFormula
end
end
