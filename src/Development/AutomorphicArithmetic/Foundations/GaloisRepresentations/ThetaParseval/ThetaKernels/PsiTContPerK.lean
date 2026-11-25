module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertKStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequence
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

/-! # PsiTContPerK: Consolidated global theta-kernel definitions and proofs (PsiTContPerK). -/
@[expose] public section

noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open GlobalTheory.Doubling (absE)
open GlobalTheory.Eis (cosetSum term)

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open GlobalTheory.ThK (incV)
open Matrix (fromBlocks transpose_apply submatrix_apply)
open GlobalTheory.EisBL.DoubledParabolic (inFrame_mul inFrame_inv inFrame_one)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
  PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {d : SD_k σ} {L : LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace W
variable (L) in
def Wm_k (a b : AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 - Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 +
    Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) a + Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) b
theorem Wm_mul_k (a b a' b' : AE F E) (h1 : a * a' = 1) (h2 : b * b' = 1) : Wm_k L a b * Wm_k L b' a' = 1 := by
  simp only [Wm_k, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, 
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, reduceCtorEq, not_false_eq_true, mul_one,
      one_mul,
    h1, h2]
  abel
theorem Wm_row_out_k (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    Wm_k L a b (Sum.inr k) m = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr k) m := by
  simp [Wm_k, Ne.symm hk]
theorem Wm_row_y_k (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    Wm_k L a b (Sum.inr L.i₀) m = if m = Sum.inl L.i₀ then b else 0 := by
  rcases m with i | i
  · by_cases hi : i = L.i₀
    · subst hi; simp [Wm_k]
    · simp [Wm_k, Ne.symm hi, hi]
  · by_cases hi : i = L.i₀
    · subst hi; simp [Wm_k]
    · simp [Wm_k, Ne.symm hi]
theorem Wm_col_out_k (a b : AE F E) {l : Fin d.n} (hl : l ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    Wm_k L a b m (Sum.inl l) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) m (Sum.inl l) := by
  simp [Wm_k, Ne.symm hl]
theorem Wm_col_x_k (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    Wm_k L a b m (Sum.inl L.i₀) = if m = Sum.inr L.i₀ then b else 0 := by
  rcases m with i | i
  · by_cases hi : i = L.i₀
    · subst hi; simp [Wm_k]
    · simp [Wm_k, hi, Ne.symm hi]
  · by_cases hi : i = L.i₀
    · subst hi; simp [Wm_k]
    · simp [Wm_k, hi, Ne.symm hi]
theorem mul_row_out_k (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀)
    (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : Fin d.n ⊕ Fin d.n) :
    (Wm_k L a b * M) (Sum.inr k) c = M (Sum.inr k) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr k)]
  · rw [Wm_row_out_k a b hk, Matrix.one_apply_eq, one_mul]
  · intro m _ hm
    rw [Wm_row_out_k a b hk, Matrix.one_apply_ne (Ne.symm hm), zero_mul]
  · simp
theorem mul_row_y_k (a b : AE F E) (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (c : Fin d.n ⊕ Fin d.n) : (Wm_k L a b * M) (Sum.inr L.i₀) c = b * M (Sum.inl L.i₀) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
  · rw [Wm_row_y_k, ite_eq_left rfl]
  · intro m _ hm
    rw [Wm_row_y_k, ite_eq_right hm, zero_mul]
  · simp
theorem mul_col_out_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E) {l : Fin d.n}
    (hl : l ≠ L.i₀) (r : Fin d.n ⊕ Fin d.n) : (M * Wm_k L a b) r (Sum.inl l) = M r (Sum.inl l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl l)]
  · rw [Wm_col_out_k a b hl, Matrix.one_apply_eq, mul_one]
  · intro m _ hm
    rw [Wm_col_out_k a b hl, Matrix.one_apply_ne hm, mul_zero]
  · simp
theorem mul_col_x_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E)
    (r : Fin d.n ⊕ Fin d.n) : (M * Wm_k L a b) r (Sum.inl L.i₀) = M r (Sum.inr L.i₀) * b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)]
  · rw [Wm_col_x_k, ite_eq_left rfl]
  · intro m _ hm
    rw [Wm_col_x_k, ite_eq_right hm, mul_zero]
  · simp
end W
open W in
theorem weyl_conjugate_exponential_parabolic (h : Hyp_k L nb uM nb' w₁ cM δ) {e : AE F E} {b : Fin L.n → AE F E} {s :
  d.G}
    (hs : inFrame d.b s = sExp_k L e b) : w₁ * s * w₁⁻¹ ∈ par2 σ d.Y := by
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  have hW' : inFrame d.b w₁ = W.Wm_k L (inclR (F := F) (AF F) a₀) (inclR (F := F) (AF F) b₀) := hW
  have h1 : inclR (F := F) (AF F) a₀ * inclR (F := F) (AF F) a₀⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h2 : inclR (F := F) (AF F) b₀ * inclR (F := F) (AF F) b₀⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  have hWi : inFrame d.b w₁⁻¹ = W.Wm_k L (inclR (AF F) b₀⁻¹) (inclR (AF F) a₀⁻¹) := by
    rw [inFrame_inv, hW', Matrix.inv_eq_right_inv (W.Wm_mul_k _ _ _ _ h1 h2)]
  refine (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2 ?_
  rw [inFrame_mul, inFrame_mul, hW', hs, hWi]
  have hne := C4.em_ne_k L
  have hS_rl : ∀ k l, sExp_k L e b (Sum.inr k) (Sum.inl l) = 0 := fun k l => by simp [sExp_k]
  have hS_ry : ∀ k, k ≠ L.i₀ → sExp_k L e b (Sum.inr k) (Sum.inr L.i₀) = 0 := fun k hk => by
    simp [sExp_k, hk]
  have hS_xl : ∀ l, l ≠ L.i₀ → sExp_k L e b (Sum.inl L.i₀) (Sum.inl l) = 0 := fun l hl => by
    simp [sExp_k, Ne.symm hl]
  have hS_xy : sExp_k L e b (Sum.inl L.i₀) (Sum.inr L.i₀) = 0 := by
    simp [sExp_k, Matrix.sum_apply, hne]
  ext k l
  show (W.Wm_k L _ _ * sExp_k L e b * W.Wm_k L _ _) (Sum.inr k) (Sum.inl l) = 0
  by_cases hl : l = L.i₀
  · subst hl
    rw [W.mul_col_x_k]
    by_cases hk : k = L.i₀
    · subst hk
      rw [W.mul_row_y_k, hS_xy, mul_zero, zero_mul]
    · rw [W.mul_row_out_k _ _ hk, hS_ry k hk, zero_mul]
  · rw [W.mul_col_out_k _ _ _ hl]
    by_cases hk : k = L.i₀
    · subst hk
      rw [W.mul_row_y_k, hS_xl l hl, mul_zero]
    · rw [W.mul_row_out_k _ _ hk, hS_rl]
theorem normalize_k (h : Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬
  FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ Fix_k L (w₁⁻¹ * (p * γ)) :=
  N.normalize_k h hγ hn
theorem stab_dec_k (h : Hyp_k L nb uM nb' w₁ cM δ) {x : d.G} (hx : x ∈ rat2 σ d.Y) (hf : Fix_k L x) :
    ∃ (s : d.G) (c : Cr_k L) (γ' : G2 σ L.Y), s ∈ rat2 σ d.Y ∧ w₁ * s * w₁⁻¹ ∈ par2 σ d.Y ∧ γ' ∈ rat2 σ L.Y ∧
      inFrame L.b γ' = (inFrame d.b x).submatrix (C4.emS_k L)
        (C4.emS_k L) ∧ x = s * (cM c.1 * L.j γ') := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) x hx
  have hx0 : ∀ r, G0 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    apply kfour.inclR_injective (F := F)
    have h1 := hf r
    rw [hG0] at h1
    simp only [incM, Matrix.map_apply] at h1
    rw [h1]
    by_cases hr : r = Sum.inl L.i₀ <;> simp [Matrix.one_apply, hr]
  have hform := form_E hε x hG0
  have hy := yrow_zero hform hx0
  set H := G0.submatrix (C4.emS_k L)
    (C4.emS_k L) with hH_def
  have hH := C4.Bq.blockH_form_k L hform hx0 hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨g', hg'⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hg'r : g' ∈ rat2 σ L.Y := kunf.rat_of_inFrame hg'
  have hg'i : inFrame L.b g'⁻¹ = incM F H' := by
    rw [inFrame_inv, hg']
    exact Matrix.inv_eq_right_inv hIA
  set n := x * L.j g'⁻¹ with hn_def
  have hnF : inFrame d.b n = incM F (G0 * C4.padE_k L H') := by
    rw [hn_def, inFrame_mul, hG0,
      C4.inFrame_j_k, hg'i,
      C4.padM_incM_k, kfour.incM_mul']
  have hnq0 : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (G0 * C4.padE_k L H') :=
    C4.Bq.nq_E_k L hx0 hy hHH'
  have hnr : n ∈ rat2 σ d.Y := mul_mem hx (C4.j_rat_k L (inv_mem hg'r))
  set N0 := G0 * C4.padE_k L H' with hN0
  set u₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inl (L.em j)) with hu₀
  set b₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inr (L.em j)) with hb₀
  set z₀ : E := N0 (Sum.inl L.i₀) (Sum.inr L.i₀) + ∑ j, b₀ j * σ (u₀ j) with hz₀
  have hUN0 : M.U (σ : E →+* E) (((ε : ℤ) : E)) N0 := form_E hε n hnF
  have hpz : σ z₀ = -(((ε : ℤ) : E) * z₀) := M.even_im_hermitian_sub hσ hε1 hεσ L.em L.inj L.rng hUN0 hnq0
  have hpd := delta_par_k h hε
  have hε0 : (((ε : ℤ) : E)) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε1; exact zero_ne_one hε1
  have hfix : σ (z₀ / δ) = z₀ / δ := by
    rw [map_div₀, hpz, hpd, neg_div_neg_eq, mul_div_mul_left _ _ hε0]
  obtain ⟨a₀, ha₀⟩ := fixed_in_F d.ok.good.cm (z₀ / δ) hfix
  let c : Cr_k L := ⟨(incV F u₀, algebraMap F (AF F) a₀), AddSubgroup.subset_closure ⟨u₀, rfl⟩, ⟨a₀,
    rfl⟩⟩
  set s := n * (cM c.1)⁻¹ with hs_def
  have hsr : s ∈ rat2 σ d.Y := mul_mem hnr (inv_mem (cM_rat'_k h c.2.1 c.2.2))
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom e = e := map_intCast _ _
  have hN : inFrame d.b n = sExp_k L e (incV F b₀) * inFrame d.b (cM c.1) := by
    apply M.nq_unique (s := (cA σ).toRingHom) (e := e) (i₀ := L.i₀) (cA_inv' hσ) he hse
    · exact kunf.frame_eq hε n
    · have hUS := U_sExp_k (ε := ε) (L := L) hσ (incV F b₀)
      have hUC : M.U (cA σ).toRingHom e (inFrame d.b (cM c.1)) := kunf.frame_eq hε (cM c.1)
      unfold M.U at hUS hUC ⊢
      rw [Matrix.transpose_mul, Matrix.map_mul]
      calc (inFrame d.b (cM c.1))ᵀ * (sExp_k L e (incV F b₀))ᵀ * kunf.jw d.n e *
            ((sExp_k L e (incV F b₀)).map (cA σ).toRingHom * (inFrame d.b (cM c.1)).map (cA
              σ).toRingHom)
          = (inFrame d.b (cM c.1))ᵀ * ((sExp_k L e (incV F b₀))ᵀ * kunf.jw d.n e *
            (sExp_k L e (incV F b₀)).map (cA σ).toRingHom) * (inFrame d.b (cM c.1)).map (cA
              σ).toRingHom := by
            simp only [Matrix.mul_assoc]
        _ = kunf.jw d.n e := by rw [hUS, hUC]
    · rw [hnF]; exact NQ.map _ hnq0
    · exact NQ.mul (nq_sExp_k _ _) (nq_cM_k h _)
    · obtain ⟨r1, r2, r3,
        r4⟩ := row_sC_k h e (incV F b₀) (incV F u₀) (algebraMap F (AF F) a₀)
      intro c'
      rw [hnF]
      rcases c' with k | k
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r4]
          have := hnq0.1 (Sum.inl L.i₀)
          simp only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
          simp [incM, this]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r1]; rfl
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r3]
          have e1 : algebraMap F (AF F) a₀ • inclR (F := F) (AF F) δ = inclR (F := F) (AF F) z₀ := by
            have : z₀ = algebraMap F E a₀ * δ := by rw [ha₀, div_mul_cancel₀ _ h.δ0]
            rw [this, map_mul]
            show algebraMap F (AF F) a₀ • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (algebraMap F E a₀) * (1 : AF F) ⊗ₜ[F]
              δ
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
                ← Algebra.algebraMap_eq_smul_one]
          rw [e1, hz₀]
          have hcA : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => rfl
          simp [incM, incV, hcA, map_add (f := _), map_sum, map_mul]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r2]; rfl
  have hS : inFrame d.b s = sExp_k L e (incV F b₀) := by
    have h1 : inFrame d.b (cM c.1) * inFrame d.b (cM c.1)⁻¹ = 1 := by
      rw [← inFrame_mul, mul_inv_cancel,
        inFrame_one]
    rw [hs_def, inFrame_mul, hN, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine ⟨s, c, g', hsr, weyl_conjugate_exponential_parabolic h hS, hg'r, ?_, ?_⟩
  · rw [hg', hG0]; rfl
  · rw [hs_def, hn_def, map_inv]; group
theorem paddedMatrix_mul_submatrix (A : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (C4.padM_k L A * N).submatrix
      (C4.emS_k L) (C4.emS_k
      L) = A * N.submatrix (C4.emS_k L)
      (C4.emS_k L) := by
  ext a c
  simp only [submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (C4.emS_k L)
    (C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [C4.padM_out_col_k L A _ hl', Matrix.one_apply_ne, zero_mul]
    rintro rfl
    exact hl' ⟨a, rfl⟩
  · intro b
    rw [C4.padM_emS_k]
theorem mul_paddedMatrix_submatrix (B : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (N * C4.padM_k L B).submatrix
      (C4.emS_k L) (C4.emS_k
      L) = N.submatrix (C4.emS_k L)
      (C4.emS_k L) * B := by
  ext a c
  simp only [submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (C4.emS_k L)
    (C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [C4.padM_out_row_k L B hl', Matrix.one_apply_ne, mul_zero]
    rintro rfl
    exact hl' ⟨c, rfl⟩
  · intro b
    rw [C4.padM_emS_k]
theorem conj_rationalParabolic_embed (h : Hyp_k L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈
  rat2 σ L.Y) (c : Cr_k L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : Cr_k L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) := by
  have hx :=
    mul_mem (mul_mem (inv_mem (C4.j_rat_k L hpr)) (cM_rat'_k h c.2.1
      c.2.2)) (C4.j_rat_k L hpr)
  have hf :=
    fix_mul_k (fix_mul_k (fix_inv_k (fix_j_k p')) (fix_cM'_k h c.1)) (fix_j_k p')
  obtain ⟨s, c₂, γ', hs, hsP, -, hγ', hx'⟩ := stab_dec_k h hx hf
  have hsub : (inFrame d.b ((L.j p')⁻¹ * cM c.1 * L.j p')).submatrix
    (C4.emS_k L) (C4.emS_k
    L) = 1 := by
    rw [inFrame_mul, inFrame_mul, ← map_inv,
      C4.inFrame_j_k,
      C4.inFrame_j_k,
      mul_paddedMatrix_submatrix, paddedMatrix_mul_submatrix, emS_cM_k h, Matrix.mul_one,
        ← inFrame_mul, inv_mul_cancel,
      inFrame_one]
  have hγ1 : γ' = 1 := kunf.inFrame_injective L.b (by rw [hγ', hsub, inFrame_one])
  rw [hγ1, map_one, mul_one] at hx'
  refine ⟨L.j p' * (w₁ * s * w₁⁻¹), mul_mem (C4.j_par_k L hp) hsP,
    mul_mem (C4.j_rat_k L hpr) (mul_mem (mul_mem h.wr hs) (inv_mem h.wr)),
      c₂, ?_⟩
  have hw := weyl_commutes_embedding h p'
  calc w₁ * (cM c.1 * L.j p') = w₁ * L.j p' * ((L.j p')⁻¹ * cM c.1 * L.j p') := by group
    _ = L.j p' * w₁ * (s * cM c₂.1) := by rw [hw, hx']
    _ = L.j p' * (w₁ * s * w₁⁻¹) * (w₁ * cM c₂.1) := by group
theorem inj_core_k (h : Hyp_k L nb uM nb' w₁ cM δ) {p : d.G} (hp : p ∈ par2 σ d.Y) (hpr : p ∈ rat2 σ d.Y) {c c' : Cr_k
  L}
    {γ' γ'' : G2 σ L.Y} (h' : γ' ∈ rat2 σ L.Y) (h'' : γ'' ∈ rat2 σ L.Y)
    (e : p * (w₁ * (cM c.1 * L.j γ')) = w₁ * (cM c'.1 * L.j γ'')) :
    γ'' * γ'⁻¹ ∈ par2 σ L.Y ∧ (γ'' = γ' → c = c') :=
  I.inj_core_k h hp hpr h' h'' e
theorem conj_par_k (h : Hyp_k L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈ rat2 σ L.Y) (c :
  Cr_k L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : Cr_k L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) :=
      conj_rationalParabolic_embed h hp hpr c
theorem second_orbit_bijection_weyl (h : Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : Cs_k L.sd,
      Cr_k L) ≃ {q : Cs_k d // ¬
      FirstOrbit L (rep_k
      q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j
        (rep_k x.1))) := by
  have hg : ∀ x : (Σ _ : Cs_k L.sd, Cr_k L),
    w₁ * (cM x.2.1 * L.j (rep_k x.1)) ∈ rat2 σ d.Y := fun x =>
    (rat2 σ d.Y).mul_mem h.wr ((rat2 σ d.Y).mul_mem (cM_rat'_k h x.2.2.1 x.2.2.2)
      (C4.j_rat_k L (rep_mem_k L.sd x.1)))
  have hfix : ∀ x : (Σ _ : Cs_k L.sd, Cr_k L),
    Fix_k L (cM x.2.1 * L.j (rep_k x.1)) := fun x => fix_mul_k (fix_cM'_k
    h _) (fix_j_k _)
  let Fm : (Σ _ : Cs_k L.sd,
    Cr_k L) → {q : Cs_k d // ¬
    FirstOrbit L (rep_k q)}
    := fun x =>
    ⟨Quotient.mk _ ⟨_, hg x⟩, by
      obtain ⟨p, hp, -, e⟩ := out_mk_k d ⟨_, hg x⟩
      rw [e, first_orbit_parabolic_left hp]
      exact not_first_orbit_weyl h (hfix x)⟩
  have hinj : Function.Injective Fm := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ hE
    have hE' := congrArg Subtype.val hE
    rw [mk_eq_mk_k] at hE'
    set g₁ := w₁ * (cM c₁.1 * L.j (rep_k q₁))
    set g₂ := w₁ * (cM c₂.1 * L.j (rep_k q₂))
    have e : (g₂ * g₁⁻¹) * (w₁ * (cM c₁.1 * L.j (rep_k q₁))) = w₁ * (cM
      c₂.1 * L.j (rep_k q₂)) := by
      simp only [g₁, g₂]; group
    have hpr : g₂ * g₁⁻¹ ∈ rat2 σ d.Y := (rat2 σ d.Y).mul_mem (hg ⟨q₂, c₂⟩) ((rat2 σ d.Y).inv_mem (hg ⟨q₁, c₁⟩))
    obtain ⟨hP, hc⟩ := inj_core_k h hE' hpr (rep_mem_k L.sd q₁) (rep_mem_k L.sd q₂) e
    have hq : q₁ = q₂ := by
      rw [← mk_rep_k L.sd q₁, ← mk_rep_k L.sd q₂, mk_eq_mk_k]
      exact hP
    subst hq
    rw [hc rfl]
  have hsurj : Function.Surjective Fm := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hp, hpr, hfx⟩ := normalize_k h (rep_mem_k d q) hq
    have hr :=
      (rat2 σ d.Y).mul_mem ((rat2 σ d.Y).inv_mem h.wr) ((rat2 σ d.Y).mul_mem hpr (rep_mem_k d q))
    obtain ⟨s, c, γ', hsr, hW, hγ', -, hx⟩ := stab_dec_k h hr hfx
    obtain ⟨p', hp', hp'r, he'⟩ := out_mk_k L.sd ⟨γ', hγ'⟩
    obtain ⟨p₂, hp₂, hp₂r, c₂, hc₂⟩ := conj_par_k h ((par2 σ L.Y).inv_mem hp') ((rat2 σ L.Y).inv_mem hp'r) c
    refine ⟨⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩, Subtype.ext ?_⟩
    show (Quotient.mk _ ⟨_, hg ⟨Quotient.mk _ ⟨γ', hγ'⟩,
      c₂⟩⟩ : Cs_k d) = q
    conv_rhs => rw [← mk_rep_k d q]
    rw [mk_eq_mk_k]
    have hγ'' : γ' = p'⁻¹ * rep_k (Quotient.mk _ ⟨γ',
      hγ'⟩ : Cs_k L.sd) := by rw [he']; group
    have key : p * rep_k q = (w₁ * s * w₁⁻¹) * p₂ * (w₁ * (cM c₂.1 * L.j
      (rep_k (Quotient.mk _ ⟨γ',
      hγ'⟩ : Cs_k L.sd)))) := by
      have h1 : p * rep_k q = w₁ * (s * (cM c.1 * L.j γ')) :=
        by rw [← hx]; group
      rw [h1]
      conv_lhs => rw [hγ'', map_mul]
      have h2 : w₁ * (s * (cM c.1 * (L.j p'⁻¹ * L.j (rep_k (Quotient.mk _
        ⟨γ', hγ'⟩ : Cs_k L.sd))))) =
          (w₁ * s * w₁⁻¹) * ((w₁ * (cM c.1 * L.j p'⁻¹)) * L.j (rep_k
            (Quotient.mk _ ⟨γ', hγ'⟩ : Cs_k L.sd))) := by group
      rw [h2, hc₂]
      group
    have : rep_k q * (w₁ * (cM c₂.1 * L.j
      (rep_k (Quotient.mk _ ⟨γ',
      hγ'⟩ : Cs_k L.sd))))⁻¹ = p⁻¹ * ((w₁ * s * w₁⁻¹) * p₂) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, key]; group
    rw [this]
    exact (par2 σ d.Y).mul_mem ((par2 σ d.Y).inv_mem hp) ((par2 σ d.Y).mul_mem hW hp₂)
  refine ⟨Equiv.ofBijective Fm ⟨hinj, hsurj⟩, fun x => ?_⟩
  obtain ⟨p, hp, hpr, e⟩ := out_mk_k d ⟨_, hg x⟩
  exact ⟨p, hp, hpr, e⟩
end PositivityTheory.SiegelWeilFormula.Act.C6
end

namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
abbrev Crat_k (L : LD_k d) : Type := {c : (Fin L.n → AE F E) × AF F // c.1 ∈ L.ratV ∧ c.2 ∈ (algebraMap F (AF F)).range}
theorem second_orbit_bijection (h : Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : Cs_k L.sd,
      Crat_k L) ≃ {q : Cs_k d // ¬
      FirstOrbit L (rep_k
      q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j
        (rep_k x.1))) := C6.second_orbit_bijection_weyl ⟨h.nb, h.uM, h.nb', h.wr, h.wf,
    h.cf, h.δ0⟩
end PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {d : SD_k σ} (L : LD_k d)
def padZeroAlt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0
theorem pad_zero_embedding (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : padZeroAlt L β (L.em a) (L.em c)
  = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [padZeroAlt, dite_eq_left h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]
theorem pad_zero_outside (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : padZeroAlt L β i k = 0 := by
  simp only [padZeroAlt, dite_eq_right h]
theorem pad_zero_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (padZeroAlt L β i k) (padZeroAlt L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [pad_zero_embedding, pad_zero_embedding]
    exact h1 a c
  · rw [pad_zero_outside L β i k h, pad_zero_outside L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0
theorem eps_common_k : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee := Afc.eps_eq_k L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩
theorem pad_zero_mem_unipotent (β : nA σ L.Y L.b) : padZeroAlt L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := eps_common_k L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine pad_zero_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this
def padN_k : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨padZeroAlt L β.1, pad_zero_mem_unipotent L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine pad_zero_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_embedding]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_outside L _ i k h, add_zero]
theorem prj_padN_k (β : nA σ L.Y L.b) : prj_k L (padN_k L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [prj_val_k, submatrix_apply]
  exact pad_zero_embedding L β.1 a c
theorem continuous_padN_k : Continuous (padN_k L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [pad_zero_embedding]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtypeVal)
  · simp only [pad_zero_outside L _ i k h]
    exact continuous_const
theorem prj_nF_k {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [prj_val_k, hT]
  rfl
theorem padN_nF_k {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : padN_k L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show padZeroAlt L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [padZeroAlt, dite_eq_left h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dite_eq_left h]
  · rw [padZeroAlt, dite_eq_right h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dite_eq_right h, map_zero]
theorem fiber_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (prj_k L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := eps_common_k L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact _root_.GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq (prj_k L) (padN_k L) (continuous_prj_k L) (continuous_padN_k L)
    (prj_padN_k L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => prj_nF_k L hγ)
    (fun γ hγ => padN_nF_k L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)
theorem phz_eq_flat_k {s₁ z : ℂ} {f : d.G → ℂ} : phz_k d f s₁ z = flat d.a
  f s₁ z := by
  funext x
  simp only [phz_k, GlobalTheory.ThK.Dbl.flat,
    kunf.ht_eq_k]
theorem phz_law_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    Law d.χ (z - s₁ + (s₁ + (d.n : ℂ) / 2)) (phz_k d f s₁ z) := by
  rw [phz_eq_flat_k]
  exact Law.flat hf.law d.ok.hgt (kunf.a_pos_k d) z
theorem phz_par_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ht : Matrix.GeneralLinearGroup.det t = 1) (g : d.G) :
      phz_k d f s₁ z (p * g) =
      phz_k d f s₁ z g := by
  rw [phz_law_k hf z p t g hp, ht, map_one, map_one]
  simp
theorem phz_rat_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} (hp : p ∈ par2 σ d.Y)
    (hr : p ∈ rat2 σ d.Y) (g : d.G) : phz_k d f s₁ z (p * g) =
      phz_k d f s₁ z g :=
  (phz_law_k hf z).rat d.ok.hecke hp hr g
theorem key_id_k {nb : nA σ d.Y d.b → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : nA σ d.Y d.b) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (prj_k L β)) * x) := key_id_pf_k L hnb hnb' hU h β u x
theorem tr_sub_k {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * β.1) = Matrix.trace (T'.1.1 * (prj_k L β).1) := by
  obtain ⟨h0, h1⟩ := hT
  have hout : ∀ i, i ∉ Set.range L.em → i = L.i₀ := fun i hi => by
    by_contra h
    exact hi ((L.rng i).1 h)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, prj_val_k, h1, submatrix_apply]
  symm
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun a => ?_)
  · rw [hout i hi]
    simp [(h0 _).1]
  · refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun b => rfl)
    rw [hout k hk]
    simp [(h0 _).2]
theorem cos_bij_k : ∃ e : Cs_k L.sd ≃ {q :
  Cs_k d // FirstOrbit L
  (rep_k q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    rep_k (e q').1 = p * L.j
      (rep_k q') := cos_bij_pf_k L
end PositivityTheory.SiegelWeilFormula.Act.C4

section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ} (L : LD_k d)
instance countableCs_k (d : SD_k σ) : Countable (Cs_k d) := by
  have := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  infer_instance
theorem cont_E_k {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f)
    (hmaj : ∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ,
      Summable u ∧ ∀ g ∈ C, ∀ q,
      ‖term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q)
    {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b nb') (x : d.G) :
    Continuous fun β' : nA σ L.Y L.b => ∑' q' : Cs_k L.sd,
      phz_k d f s₁ z (L.j
      (rep_k q' * nb' β') * x) := by
  obtain ⟨e, he⟩ := cos_bij_k L
  have hphz : Continuous (phz_k d f s₁ z) := by
    rw [phz_eq_flat_k]
    exact continuous_flat hf.cont (kunf.continuous_a_k d)
      (kunf.a_pos_k d) z
  have hg : Continuous fun β' : nA σ L.Y L.b => L.j (nb' β') * x :=
    (L.cont.comp (kunf.continuous_nb hnb')).mul continuous_const
  have hterm : ∀ q' β',
    phz_k d f s₁ z (L.j
    (rep_k q' * nb' β') * x) =
      phz_k d f s₁ z (rep_k
        (e q').1 * (L.j (nb' β') * x)) := by
    intro q' β'
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he q'
    rw [hrep, mul_assoc, phz_rat_k hf z hp₀ hr₀, map_mul, mul_assoc]
  refine continuous_iff_continuousAt.2 fun β₀ => ?_
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (L.j (nb' β₀) * x)
  obtain ⟨u, hu, hbd⟩ := hmaj C hCc
  have hN := hg.continuousAt.preimage_mem_nhds hC
  refine (continuousOn_tsum (u := u ∘ Subtype.val ∘ e) (fun q' => ?_) (hu.comp_injective
    (Subtype.val_injective.comp e.injective)) (fun q' β' hβ' => ?_)).continuousAt hN
  · exact (hphz.comp ((L.cont.comp (continuous_const.mul (kunf.continuous_nb hnb'))).mul continuous_const)).continuousOn
  · rw [hterm]
    exact hbd _ hβ' _
theorem per_E_k {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b
  nb')
    (x : d.G) (β₀ : nA σ L.Y L.b) (h₀ : β₀ ∈ nF σ L.Y L.b) (β' : nA σ L.Y L.b) :
    ∑' q' : Cs_k L.sd,
      phz_k d f s₁ z (L.j
      (rep_k q' * nb' (β₀ + β')) * x) =
      ∑' q' : Cs_k L.sd,
        phz_k d f s₁ z (L.j
        (rep_k q' * nb' β') * x) := by
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y) (fun y : G2 σ L.Y =>
    phz_k d f s₁ z (L.j y * x)) := by
    intro γ hγ g
    simp only [map_mul, mul_assoc]
    exact phz_rat_k hf z (j_par_k L (Subgroup.mem_inf.1 hγ).1) (j_rat_k L (Subgroup.mem_inf.1 hγ).2) _
  have h := GlobalTheory.Eis.leftInv_cosetSum hinv (nb' β₀) (kunf.nb_rat hnb' h₀) (nb' β')
  simp only [cosetSum, term] at h
  rw [kunf.nb_add hnb']
  exact h
theorem psiT_cont_per_k (T' : nF σ L.Y L.b) :
    Continuous (fun β' : nA σ L.Y L.b => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))) ∧
    ∀ β₀ ∈ nF σ L.Y L.b, ∀ β' : nA σ L.Y L.b,
      d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * (β₀ + β').1)))) =
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1)))) := by
  have hstd := d.ok.good.std
  refine ⟨?_, fun β₀ h₀ β' => ?_⟩
  · have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
    have htr :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
    exact hstd.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtypeVal).matrix_trace)).neg
  · have h1 := kunf.psi_rat hstd T' ⟨β₀, h₀⟩
    rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, h1, inv_one, one_mul]
theorem firstEq_of_k : AbsConv_k →
  FirstEq_k := by
  intro hA F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨t₁, ht₁⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t₂, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨max t₁ t₂, fun z hz nb lam 𝓖 hc hGc nb' lam' 𝓖' hc' hGc' uM ν 𝓤 hU hUc T T' hT x => ?_⟩
  have hz₁ : t₁ < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz₂ : t₂ < z.re := lt_of_le_of_lt (le_max_right _ _) hz
  obtain ⟨hint, hsum⟩ := ht₁ z hz₁ nb lam 𝓖 hc hGc uM ν 𝓤 hU hUc T x
  obtain ⟨e, he'⟩ := cos_bij_k L
  have : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (ν.restrict 𝓤) := ⟨by rw [Measure.restrict_apply_univ, hU.2.2.2]; exact ENNReal.one_lt_top⟩
  set ψT : nA σ L.Y L.b → ℂ := fun β' => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))
    with hψT
  set H : Cs_k L.sd → nA σ L.Y L.b → ℂ := fun q' β' =>
    phz_k d f s₁ z (L.j
    (rep_k q' * nb' β') * x) * ψT β' with hH
  have hpt : ∀ q' (pr : (Fin L.n → AE F E) × nA σ d.Y d.b),
      kq_k L f s₁ z nb T uM
        (rep_k (e q').1) x pr = H q' (prj_k L pr.2) := by
    rintro q' ⟨u, β⟩
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he' q'
    obtain ⟨p₁, t, hp₁, hdet,
      hid⟩ := key_id_k L hc.1 hc'.1 hU (rep_k q') β u x
    simp only [kq_k, hH, hψT]
    rw [hrep, mul_assoc, phz_rat_k hf z hp₀ hr₀, hid, phz_par_k hf z hp₁ hdet, tr_sub_k L hT β]
  have hν1 : (ν.restrict 𝓤).real Set.univ = 1 := by
    simp [Measure.real, hU.2.2.2]
  have hkq : ∀ q',
    kq_k L f s₁ z nb T uM
    (rep_k (e q').1) x = fun pr => H q' (prj_k L pr.2) := fun q' => funext
    (hpt q')
  have htm : ∀ q',
    tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤
    (rep_k (e q').1) x = ∫ β in 𝓖, H q' (prj_k L β) ∂lam := by
    intro q'
    have h1 : ∀ u,
      fc d.B.ψ d.b nb lam 𝓖 (fun g => phz_k d f s₁ z
      (rep_k (e q').1 * g)) T (uM u * x) =
        ∫ β in 𝓖, H q' (prj_k L β) ∂lam := by
      intro u
      refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
      exact hpt q' (u, β)
    simp only [tm_k, h1]
    rw [setIntegral_const]
    simp [Measure.real, hU.2.2.2]
  have hint' : ∀ q', Integrable (fun β => H q' (prj_k L β)) (lam.restrict 𝓖) := by
    intro q'
    have h1 := (hint (e q').1).integral_prod_right
    rw [hkq] at h1
    simpa only [integral_const, hν1, one_smul] using h1
  have hnorm : ∀ q', ∫ pr,
    ‖kq_k L f s₁ z nb T uM
    (rep_k (e q').1) x pr‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      ∫ β in 𝓖, ‖H q' (prj_k L β)‖ ∂lam := by
    intro q'
    have hI := (hint (e q').1).norm
    rw [integral_prod _ hI]
    simp only [hkq, integral_const, hν1, one_smul]
  have hsum' : Summable fun q' => ∫ β in 𝓖, ‖H q' (prj_k L β)‖ ∂lam := by
    have h2 := hsum.comp_injective (Subtype.val_injective.comp e.injective)
    exact h2.congr fun q' => hnorm q'
  set G : nA σ L.Y L.b → ℂ := fun β' => (∑' q' : Cs_k L.sd,
    phz_k d f s₁ z (L.j
    (rep_k q' * nb' β') * x)) * ψT β' with hG
  have hHG : ∀ β', ∑' q', H q' β' = G β' := fun β' => tsum_mul_right
  have hGc : Continuous G := by
    refine (cont_E_k L hf (hmaj z hz₂).1 hc'.1 x).mul (psiT_cont_per_k L T').1
  have hGp : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β' := by
    intro β₀ h₀ β'
    simp only [hG, hψT]
    rw [per_E_k L hf hc'.1 x β₀ h₀ β', (psiT_cont_per_k L T').2 β₀ h₀ β']
  calc ∑' q : {q : Cs_k d //
         FirstOrbit L (rep_k
         q)},
         tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤
         (rep_k q.1) x
      = ∑' q',
        tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤
        (rep_k (e q').1) x :=
        (e.tsum_eq (fun q => tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤
          (rep_k q.1) x)).symm
    _ = ∑' q', ∫ β in 𝓖, H q' (prj_k L β) ∂lam := tsum_congr htm
    _ = ∫ β in 𝓖, ∑' q', H q' (prj_k L β) ∂lam := by
        have := countableCs_k L.sd
        exact integral_tsum_of_summable_integral_norm hint' hsum'
    _ = ∫ β in 𝓖, G (prj_k L β) ∂lam := by simp only [hHG]
    _ = ∫ β' in 𝓖', G β' ∂lam' := fiber_k L hc hc' G hGc hGp
    _ = first_k L f s₁ z nb' lam' 𝓖' T' x := by
        simp only [first_k, fc, cosetSum,
          term, mul_one, hG, hψT]
        rfl
end PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act
theorem firstEq_k : FirstEq_k := C4.firstEq_of_k absConv_k
end PositivityTheory.SiegelWeilFormula.Act
end
end

section
open scoped ENNReal
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem eisenstein_second_term_expand (_h : Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f)
  (z : ℂ)
    {e : (Σ _ : Cs_k L.sd,
      Crat_k L) ≃ {q : Cs_k d // ¬
      FirstOrbit L (rep_k
      q)}}
    (he : ∀ x, ∃ p ∈ par2 σ d.Y,
      p ∈ rat2 σ d.Y ∧ rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j
      (rep_k x.1)))) (g : d.G) :
    eisensteinSecondTerm L (phz_k d f s₁ z) g = ∑' x : (Σ _ :
      Cs_k L.sd, Crat_k L),
      phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j
      (rep_k x.1) * g))) ∧
      ∑' q : {q : Cs_k d // ¬
        FirstOrbit L (rep_k
        q)},
        ‖phz_k d f s₁ z
        (rep_k q.1 * g)‖ₑ =
        ∑' x : (Σ _ : Cs_k L.sd, Crat_k L),
          ‖phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j
          (rep_k x.1) * g)))‖ₑ := by
  have key : ∀ x : (Σ _ : Cs_k L.sd, Crat_k L),
    phz_k d f s₁ z (rep_k (e
    x).1 * g) =
      phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j
        (rep_k x.1) * g))) := fun x => by
    obtain ⟨p, hp, hr, hx⟩ := he x
    rw [hx, mul_assoc, C4.phz_rat_k hf z hp hr, mul_assoc, mul_assoc]
  constructor
  · rw [eisensteinSecondTerm, ← e.tsum_eq]
    exact tsum_congr key
  · rw [← e.tsum_eq]
    exact tsum_congr fun x => by rw [key]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
