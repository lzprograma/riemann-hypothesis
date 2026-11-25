module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousOfLevelRealK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertKStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.HomExtensionByZeroOrthDecompRational
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum

/-! # SchrodingerModelIntertwining: Consolidated global theta-kernel definitions and proofs (SchrodingerModelIntertwining). -/
@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open GlobalTheory.Doubling (absE)
open Matrix (fromBlocks fromBlocks_multiply single_apply transpose_mul transpose_one transpose_apply mulVec_mulVec)
open GlobalTheory.EisBL.DoubledGroupTopology (continuous_cA)
open GlobalTheory.EisBL.DoubledParabolic (inFrame_mul inFrame_one)
open Finset (sum_add_distrib sum_ite_eq')

section
abbrev _root_.GlobalTheory.T.schrodinger_model_intertwining :=
  GlobalTheory.ThetaOntoF.exists_thV_eqF_k
end

section
set_option linter.unusedSectionVars false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ}
theorem nilpotentMap_add (d : SD_k σ) (a : E) : σ (σ a) = a :=
  kfour.sigma_sigma_of_good_k d.ok.good a
theorem cc_k (d : SD_k σ) (z : AE F E) : cA σ (cA σ z) = z := kfour.cA_cA' σ (nilpotentMap_add d) z
theorem idx_k (L : LD_k d) (i : Fin d.n) : i = L.i₀ ∨ ∃ k, i = L.em k := by
  by_cases h : i = L.i₀
  · exact Or.inl h
  · obtain ⟨k, hk⟩ := (L.rng i).1 h
    exact Or.inr ⟨k, hk.symm⟩
theorem sum_split_k {M : Type} [AddCommMonoid M] (L : LD_k d) (f : Fin d.n → M) :
    ∑ i, f i = f L.i₀ + ∑ k, f (L.em k) := by
  have himg : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [L.rng i]
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L.i₀), ← himg, Finset.sum_image (fun a _ b _ h => L.inj h)]
theorem uA_mul_neg_k (L : LD_k d) (u : Fin L.n → AE F E) : uA_k L u * uA_k L (-u) = 1 := by
  have e : ∀ v, uA_k L v = 1 + ComplexParameterFamilyContinuity.unipotentNilpotentPart L v := fun v => rfl
  have hs : ComplexParameterFamilyContinuity.unipotentNilpotentPart L u +
    ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u) = 0 := by
    simp only [ComplexParameterFamilyContinuity.unipotentNilpotentPart, ← sum_add_distrib, Pi.neg_apply,
      ← Matrix.single_add, add_neg_cancel, 
      Matrix.single_zero, Finset.sum_const_zero]
  rw [e, e]
  calc (1 + ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) * (1 +
         ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u)) = 1 +
         (ComplexParameterFamilyContinuity.unipotentNilpotentPart L u +
         ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u)) +
         ComplexParameterFamilyContinuity.unipotentNilpotentPart L u *
         ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u) := by
        noncomm_ring
    _ = 1 := by rw [hs, ComplexParameterFamilyContinuity.unipotent_nilpotent_mul_eq_zero]; simp
theorem blockDiagonal_preserves_form_iff (x : d.G) (h21 : (inFrame d.b x).toBlocks₂₁ = 0) :
    ((inFrame d.b x).toBlocks₁₁)ᵀ * ((inFrame d.b x).toBlocks₂₂).map (cA σ) = 1 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hf := kunf.frame_eq hε x
  set M := inFrame d.b x with hMdef
  have hM : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21]; exact (Matrix.fromBlocks_toBlocks M).symm
  rw [hM] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  exact h12
theorem lr_of_k {x : d.G} {a β D ainv : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = fromBlocks a β 0 D) (ha : a * ainv = 1) : D = ainvᵀ.map (cA σ) := by
  have hx := blockDiagonal_preserves_form_iff x (by rw [h]; rfl)
  rw [h] at hx
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂] at hx
  have e2 : D.map (cA σ) = ainvᵀ := by
    calc D.map (cA σ) = (ainvᵀ * aᵀ) * D.map (cA σ) := by
          rw [← transpose_mul, ha, transpose_one, Matrix.one_mul]
      _ = ainvᵀ := by rw [Matrix.mul_assoc, hx, Matrix.mul_one]
  rw [← e2]
  ext i j
  simp [Matrix.map_apply, cc_k d]
theorem eq_of_upper_k {x y : d.G} (hx : (inFrame d.b x).toBlocks₂₁ = 0) (hy : (inFrame d.b y).toBlocks₂₁ = 0)
    (h11 : (inFrame d.b x).toBlocks₁₁ = (inFrame d.b y).toBlocks₁₁)
    (h12 : (inFrame d.b x).toBlocks₁₂ = (inFrame d.b y).toBlocks₁₂) : x = y := by
  have ex := blockDiagonal_preserves_form_iff x hx
  have ey := blockDiagonal_preserves_form_iff y hy
  rw [h11] at ex
  have ey' : ((inFrame d.b y).toBlocks₂₂).map (cA σ) * ((inFrame d.b y).toBlocks₁₁)ᵀ = 1 := mul_eq_one_comm.1 ey
  have hD : ((inFrame d.b x).toBlocks₂₂).map (cA σ) = ((inFrame d.b y).toBlocks₂₂).map (cA σ) := by
    calc _ = (((inFrame d.b y).toBlocks₂₂).map (cA σ) * ((inFrame d.b y).toBlocks₁₁)ᵀ) *
          ((inFrame d.b x).toBlocks₂₂).map (cA σ) := by rw [ey', Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ex, Matrix.mul_one]
  have hD' : (inFrame d.b x).toBlocks₂₂ = (inFrame d.b y).toBlocks₂₂ := by
    ext i j
    have := congrArg (cA σ) (congrFun (congrFun hD i) j)
    simpa only [Matrix.map_apply, cc_k d] using this
  exact KAway.inFrame_inj_k d (Matrix.ext_iff_blocks.2 ⟨h11, h12,
    hx.trans hy.symm, hD'⟩)
variable {R : RD_k d} {L : LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem inFrame_cM_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) = fromBlocks (uA_k L c.1) (aB_k L δ c.2) 0 ((uA_k L (-c.1))ᵀ.map (cA σ)) := by
  obtain ⟨A', hA⟩ := h.cf c
  rw [hA, lr_of_k hA (uA_mul_neg_k L c.1)]
section
variable (R : RD_k d)
theorem eps_mul_k : ((R.ε : ℤ) : AE F E) * ((R.ε : ℤ) : AE F E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem eps_mulE_k : ((R.ε : ℤ) : E) * ((R.ε : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem eA_eq_k : eA_k R = ((R.ε : ℤ) : AE F E) := map_intCast _ _
end
theorem sB_i0i0_k (b : Fin L.n → AE F E) : sB_k R L b L.i₀ L.i₀ = 0 := by
  simp [sB_k, Matrix.sum_apply, Matrix.add_apply, 
    fun j => (ComplexParameterFamilyContinuity.em_ne_k L j)
    ]
theorem sB_i0em_k (b : Fin L.n → AE F E) (l : Fin L.n) : sB_k R L b L.i₀ (L.em l) = b l := by
  simp [sB_k, Matrix.sum_apply, Matrix.add_apply, single_apply,
    fun j => (ComplexParameterFamilyContinuity.em_ne_k L j),
    fun j => (ComplexParameterFamilyContinuity.em_ne_k L j).symm,
    L.inj.eq_iff]
theorem section_entry_embedded_row (b : Fin L.n → AE F E) (k : Fin L.n) : sB_k R L b (L.em k) L.i₀ = -(eA_k R * cA σ (b
  k)) := by
  simp [sB_k, Matrix.sum_apply, Matrix.add_apply, single_apply,
    fun j => (ComplexParameterFamilyContinuity.em_ne_k L j),
    fun j => (ComplexParameterFamilyContinuity.em_ne_k L j).symm,
    L.inj.eq_iff]
theorem sB_emem_k (b : Fin L.n → AE F E) (k l : Fin L.n) : sB_k R L b (L.em k) (L.em l) = 0 := by
  simp [sB_k, Matrix.sum_apply, Matrix.add_apply, 
    
    fun j => (ComplexParameterFamilyContinuity.em_ne_k L j).symm]
theorem sB_cond_k (b : Fin L.n → AE F E) : sB_k R L b ∈ kfour.nCond σ d.n R.ε := by
  show (sB_k R L b)ᵀ = -((((R.ε : ℤ) : AE F E)) • (sB_k R L b).map (cA σ))
  have e2 := eps_mul_k R
  ext i j
  rcases idx_k L i with rfl | ⟨k, rfl⟩ <;> rcases idx_k L j with rfl | ⟨l, rfl⟩ <;>
    simp only [transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, sB_i0i0_k, sB_i0em_k,
      section_entry_embedded_row,
      sB_emem_k, map_zero, smul_eq_mul, map_neg, map_mul, cc_k d, eA_eq_k]
  all_goals (try simp only [map_intCast])
  all_goals first | (simp; done) | (simp only [mul_neg, neg_neg]; rw [← mul_assoc, e2, one_mul])
theorem continuous_sB_k : Continuous (sB_k R L) := by
  unfold sB_k
  refine continuous_finsetSum _ fun j _ => Continuous.add ?_ ?_
  · have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
        fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
      funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]; exact (continuous_apply j).smul continuous_const
  · have e : (fun b : Fin L.n → AE F E => Matrix.single (L.em j) L.i₀ (-(eA_k R * cA σ (b j)))) =
        fun b => (-(eA_k R * cA σ (b j))) • Matrix.single (L.em j) L.i₀ (1 : AE F E) := by
      funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact ((continuous_const.mul ((continuous_cA σ).comp (continuous_apply
      j))).neg).smul continuous_const
theorem inFrame_sM'_k (b : Fin L.n → AE F E) : inFrame d.b (sM_k R L b) = bMat_k (sB_k R L b) := by
  have hex : ∃ x : d.G, inFrame d.b x = bMat_k (sB_k R L b) :=
    ⟨⟨kfour.nU d.b (sB_k R L b), kfour.nU_mem (nilpotentMap_add d) R.hε (sB_cond_k b)⟩, kfour.inFrame_nU _ _⟩
  unfold sM_k elt_k
  rw [dite_eq_left hex]
  exact hex.choose_spec
theorem sig_delta_k (h : Hyp_k L nb uM nb' w₁ cM δ) : σ δ = -(((R.ε : ℤ) : E)) * δ := by
  have hx : inFrame d.b (cM (0, 1)) = kfour.nM (aB_k L δ 1) := by
    rw [inFrame_cM_k h]
    simp [uA_k, kfour.nM, transpose_one]
  have hc := kfour.cond_of_inFrame R.hε (cM (0, 1)) _ hx
  have e := congrFun (congrFun hc L.i₀) L.i₀
  simp only [aB_k, transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.single_apply_same,
    one_smul, smul_eq_mul] at e
  have hcA : cA σ (inclR (F := F) (AF F) δ) = inclR (F := F) (AF F) (σ δ) := by
    show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] σ δ
    simp
  have e' : inclR (F := F) (AF F) δ = inclR (F := F) (AF F) (-(((R.ε : ℤ) : E) * σ δ)) := by
    rw [e, map_neg, map_mul, map_intCast, hcA]
  have hδ := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) e'
  have e2 := eps_mulE_k R
  linear_combination (((R.ε : ℤ) : E)) * hδ - σ δ * e2
theorem eig_k (h : Hyp_k L nb uM nb' w₁ cM δ) (y : AE F E) (hy : cA σ y = -(((R.ε : ℤ) : AE F E)) * y) :
    ellA δ y • inclR (F := F) (AF F) δ = y := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  have hδ0 := h.δ0
  have hδ : σ δ = -(((R.ε : ℤ) : E)) * δ := sig_delta_k h
  have hℓ := ellSpec (F := F) hδ0
  set ℓ := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef
  have hline : ∀ e : E, σ e = -(((R.ε : ℤ) : E)) * e → ℓ e • δ = e := by
    intro e he
    obtain ⟨c, rfl⟩ := eigLine hcm R.ε hδ0 hδ he
    rw [map_smul, hℓ, smul_eq_mul, mul_one]
  have hε2 := eps_mulE_k R
  have hψ : ∀ z : AE F E, ellA δ (z - ((R.ε : ℤ) : AE F E) * cA σ z) • inclR (AF F) δ =
      z - ((R.ε : ℤ) : AE F E) * cA σ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by
        simp [cA, Algebra.TensorProduct.map_tmul]
      have hm : ((R.ε : ℤ) : AE F E) * (a ⊗ₜ[F] σ e) = a ⊗ₜ[F] (((R.ε : ℤ) : E) * σ e) := by
        rw [← zsmul_eq_mul, ← zsmul_eq_mul, TensorProduct.tmul_smul]
      rw [hc, hm, ← TensorProduct.tmul_sub]
      have he' : σ (e - ((R.ε : ℤ) : E) * σ e) = -(((R.ε : ℤ) : E)) * (e - ((R.ε : ℤ) : E) * σ e) := by
        rw [map_sub, map_mul, map_intCast, nilpotentMap_add d]
        linear_combination (-(σ e)) * hε2
      have hl := hline _ he'
      simp only [ellA, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, AlgEquiv.toLinearMap_apply,
        Algebra.TensorProduct.rid_tmul, inclR]
      rw [show (Algebra.TensorProduct.includeRight.toRingHom δ : AE F E) = (1 : AF F) ⊗ₜ[F] δ from rfl,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
      exact congrArg (a ⊗ₜ[F] ·) hl
    | add x z hx hz =>
      rw [map_add (f := _), mul_add, add_sub_add_comm, map_add (f := _), add_smul, hx, hz]
  have key := hψ y
  rw [hy, neg_mul, mul_neg, ← mul_assoc, eps_mul_k R, one_mul, sub_neg_eq_add, map_add (f := _), add_smul] at key
  have h2 : (2 : F) • (ellA δ y • inclR (AF F) δ) = (2 : F) • y := by
    rw [two_smul, two_smul]; exact key
  exact smul_right_injective (AE F E) (two_ne_zero) h2
theorem ellA_inclR_k (_h : Hyp_k L nb uM nb' w₁ cM δ) (e : E) : ellA δ (inclR (F := F) (AF F) e) ∈ (algebraMap F (AF
  F)).range := by
  refine ⟨(Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) e, ?_⟩
  simp [ellA, inclR, LinearMap.baseChange_tmul, Algebra.algebraMap_eq_smul_one]
theorem continuous_sM'_k : Continuous (sM_k R L) := by
  have hσ := nilpotentMap_add d
  have hb := d.ok.frame
  have hnb := kfour.isNMap_nbE hσ hb
  have hmem : ∀ b, sB_k R L b ∈ nA σ d.Y d.b := fun b => (kfour.mem_nA_iff hσ R.hε _).2 (sB_cond_k b)
  have e : sM_k R L = fun b => kfour.nbE σ d.Y d.b ⟨sB_k R L b, hmem b⟩ := by
    funext b
    apply KAway.inFrame_inj_k d
    rw [inFrame_sM'_k, hnb]
    rfl
  rw [e]
  exact (kfour.nb_continuous hσ hb hnb).comp (continuous_sB_k.subtype_mk _)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end

section
set_option linter.unusedSectionVars false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.C5.JC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ}
abbrev Mt_k (d : SD_k σ) : Type := Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)
def extendByZeroColumns (L : LD_k d) (x : Fin L.n → AE F E) (i : Fin d.n) : AE F E :=
  ∑ k, (if L.em k = i then (1 : AE F E) else 0) * x k
theorem extendZeroColumn_apply_embed (L : LD_k d) (x : Fin L.n → AE F E) (k : Fin L.n) : extendByZeroColumns L x (L.em
  k) = x k := by
  simp [extendByZeroColumns, L.inj.eq_iff]
theorem extension_by_zero_at_base_index (L : LD_k d) (x : Fin L.n → AE F E) : extendByZeroColumns L x L.i₀ = 0 := by
  simp [extendByZeroColumns, ComplexParameterFamilyContinuity.em_ne_k]
def vV_k (L : LD_k d) (u b : Fin L.n → AE F E) : Fin d.n ⊕ Fin d.n → AE F E := Sum.elim (extendByZeroColumns L u)
  (extendByZeroColumns L b)
def IsPad_k (L : LD_k d) (M : Mt_k d) : Prop :=
  ∀ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    M u v = (1 : Mt_k d) u v ∧ M v u = (1 : Mt_k d) v u
theorem isPad_j_k (L : LD_k d) (g : G2 σ L.Y) : IsPad_k L (inFrame d.b (L.j g)) := L.j_out g
variable {L : LD_k d}
theorem pad_col_k {M : Mt_k d} (hM : IsPad_k L M) : M *ᵥ Pi.single (Sum.inl L.i₀) 1 = Pi.single (Sum.inl L.i₀) 1 := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [(hM _ (by simp) r).2]
  simp [Matrix.one_apply]
theorem pad_row_k {M : Mt_k d} (hM : IsPad_k L M) : Pi.single (Sum.inr L.i₀) 1 ᵥ* M = Pi.single (Sum.inr L.i₀) 1 := by
  funext r
  simp only [Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [(hM _ (by simp) r).1]
  simp [Matrix.one_apply, eq_comm]
theorem pad_vecMul_inl_k {M : Mt_k d} (hM : IsPad_k L M) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    (x ᵥ* M) (Sum.inl L.i₀) = x (Sum.inl L.i₀) := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_congr rfl fun r _ => by rw [(hM _ (by simp) r).2]]
  simp [Matrix.one_apply]
theorem pad_vecMul_inr_k {M : Mt_k d} (hM : IsPad_k L M) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    (x ᵥ* M) (Sum.inr L.i₀) = x (Sum.inr L.i₀) := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_congr rfl fun r _ => by rw [(hM _ (by simp) r).2]]
  simp [Matrix.one_apply]
theorem pad_single_vecMul_k {M : Mt_k d} (hM : IsPad_k L M) (a : AE F E) :
    Pi.single (Sum.inr L.i₀) a ᵥ* M = Pi.single (Sum.inr L.i₀) a := by
  rw [Matrix.single_vecMul]
  funext r
  simp only [Pi.smul_apply, Matrix.row_apply, smul_eq_mul]
  rw [(hM _ (by simp) r).1]
  by_cases h : r = Sum.inr L.i₀
  · subst h; simp
  · simp [h, Ne.symm h]
def hN_k (L : LD_k d) (vf wf : Fin d.n ⊕ Fin d.n → AE F E) : Mt_k d :=
  1 + Matrix.vecMulVec (Pi.single (Sum.inl L.i₀) 1) vf + Matrix.vecMulVec wf (Pi.single (Sum.inr L.i₀) 1)
theorem conj_hN_k {J K : Mt_k d} (hKJ : K * J = 1) (hJ : IsPad_k L J) (vf wf : Fin d.n ⊕ Fin d.n → AE F E) :
    J * hN_k L vf wf = hN_k L (vf ᵥ* K) (J *ᵥ wf) * J := by
  simp only [hN_k, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, pad_col_k hJ, pad_row_k hJ, Matrix.vecMul_vecMul, hKJ, Matrix.vecMul_one]
def W_k (R : RD_k d) : Mt_k d := kunf.jw d.n (((R.ε : ℤ) : AE F E))
section
variable (R : RD_k d)
theorem e_mul_e_k : (((R.ε : ℤ) : AE F E)) * ((R.ε : ℤ) : AE F E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem W_transpose_k : (W_k R)ᵀ = (((R.ε : ℤ) : AE F E)) • W_k R := by
  have he := e_mul_e_k R
  ext (i | i) (j | j) <;> simp [W_k, kunf.jw, Matrix.one_apply] <;> split_ifs <;> simp_all [eq_comm]
theorem W_mul_W_k : W_k R * W_k R = (((R.ε : ℤ) : AE F E)) • (1 : Mt_k d) := by
  simp only [W_k, kunf.jw, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
theorem W_mulVec_inl_k (y : Fin d.n ⊕ Fin d.n → AE F E) (i : Fin d.n) :
    (W_k R *ᵥ y) (Sum.inl i) = y (Sum.inr i) := by
  simp [W_k, kunf.jw, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
theorem W_mulVec_inr_k (y : Fin d.n ⊕ Fin d.n → AE F E) (i : Fin d.n) :
    (W_k R *ᵥ y) (Sum.inr i) = ((R.ε : ℤ) : AE F E) * y (Sum.inl i) := by
  simp [W_k, kunf.jw, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
end
theorem JW_k {R : RD_k d} {J K : Mt_k d} (hKJ : K * J = 1) (hK : Kᵀ * W_k R * K.map (cA σ) = W_k R) :
    J * W_k R = W_k R * (K.map (cA σ))ᵀ := by
  have he := e_mul_e_k R
  have hJt : Jᵀ * Kᵀ = 1 := by rw [← transpose_mul, hKJ, transpose_one]
  have h1 : W_k R * K.map (cA σ) = Jᵀ * W_k R := by
    calc W_k R * K.map (cA σ) = (Jᵀ * Kᵀ) * W_k R * K.map (cA σ) := by rw [hJt, Matrix.one_mul]
      _ = Jᵀ * (Kᵀ * W_k R * K.map (cA σ)) := by simp only [Matrix.mul_assoc]
      _ = Jᵀ * W_k R := by rw [hK]
  have h2 : (K.map (cA σ))ᵀ * W_k R = W_k R * J := by
    have h3 := congrArg Matrix.transpose h1
    rw [transpose_mul, transpose_mul, Matrix.transpose_transpose, W_transpose_k, Matrix.mul_smul,
      Matrix.smul_mul] at h3
    have h4 := congrArg (fun M : Mt_k d => ((R.ε : ℤ) : AE F E) • M) h3
    simpa only [smul_smul, he, one_smul] using h4
  have hWW := W_mul_W_k R
  calc J * W_k R = ((R.ε : ℤ) : AE F E) • (((R.ε : ℤ) : AE F E) • (J * W_k R)) := by rw [smul_smul, he, one_smul]
    _ = ((R.ε : ℤ) : AE F E) • ((W_k R * W_k R) * J * W_k R) :=
          by rw [hWW, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = ((R.ε : ℤ) : AE F E) • (W_k R * ((K.map (cA σ))ᵀ * W_k R) * W_k R) := by rw [h2]; simp only [Matrix.mul_assoc]
    _ = ((R.ε : ℤ) : AE F E) • (W_k R * (K.map (cA σ))ᵀ * (W_k R * W_k R)) := by simp only [Matrix.mul_assoc]
    _ = W_k R * (K.map (cA σ))ᵀ := by rw [hWW, Matrix.mul_smul, Matrix.mul_one, smul_smul, he, one_smul]
theorem cv_vecMul_k (x : Fin d.n ⊕ Fin d.n → AE F E) (K : Mt_k d) : cv σ (x ᵥ* K) = (K.map (cA σ))ᵀ *ᵥ cv σ x := by
  funext s

  simp [cv, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mul_comm]
def qf_k (R : RD_k d) (x : Fin d.n ⊕ Fin d.n → AE F E) : AE F E := x ⬝ᵥ (W_k R *ᵥ cv σ x)
theorem qf_vecMul_k {R : RD_k d} {K : Mt_k d} (hKW : K * W_k R * (K.map (cA σ))ᵀ = W_k R) (x : Fin d.n ⊕ Fin d.n → AE F
  E) :
    qf_k R (x ᵥ* K) = qf_k R x := by
  unfold qf_k
  rw [cv_vecMul_k, ← Matrix.dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hKW]
def hh_k (L : LD_k d) (u b : Fin L.n → AE F E) : AE F E := ∑ j, b j * cA σ (u j)
def wf_k (R : RD_k d) (L : LD_k d) (u b : Fin L.n → AE F E) : Fin d.n ⊕ Fin d.n → AE F E :=
  -(((R.ε : ℤ) : AE F E)) • (W_k R *ᵥ cv σ (vV_k L u b))
theorem jeA_eq_k (R : RD_k d) : eA_k R = ((R.ε : ℤ) : AE F E) := by
  simp [eA_k]
theorem uA_apply_k (u : Fin L.n → AE F E) (i k : Fin d.n) :
    uA_k L u i k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k + if i
      = L.i₀ then extendByZeroColumns L u k else 0 := by
  by_cases hi : i = L.i₀
  · subst hi
    simp [uA_k, extendByZeroColumns, Matrix.sum_apply,
      single_apply]
  · simp [uA_k, Matrix.sum_apply, Ne.symm hi, hi]
theorem D_apply_k (u : Fin L.n → AE F E) (l k : Fin d.n) :
    ((uA_k L (-u))ᵀ.map (cA σ)) l k = (1 : Matrix (Fin d.n) (Fin d.n)
      (AE F E)) l k +
      if k = L.i₀ then -cA σ (extendByZeroColumns L u l) else 0 := by
  rw [Matrix.map_apply, transpose_apply, uA_apply_k]
  by_cases hk : k = L.i₀
  · subst hk

    simp [extendByZeroColumns, Matrix.one_apply, eq_comm, map_sum, Finset.sum_neg_distrib]
  · simp [Matrix.one_apply, hk, eq_comm]
theorem sB_apply_k (R : RD_k d) (b : Fin L.n → AE F E) (i l : Fin d.n) :
    sB_k R L b i l = (if i = L.i₀ then extendByZeroColumns L b l else
      0) +
      if l = L.i₀ then -(((R.ε : ℤ) : AE F E) * cA σ (extendByZeroColumns L b i)) else 0 := by
  unfold sB_k
  simp only [Matrix.sum_apply, Matrix.add_apply, single_apply, sum_add_distrib, jeA_eq_k]
  rcases idx_k L i with rfl | ⟨p,
    rfl⟩ <;> rcases idx_k L l with rfl | ⟨q, rfl⟩ <;>

    simp [extendByZeroColumns, 
      (ComplexParameterFamilyContinuity.em_ne_k L _).symm, L.inj.eq_iff, eq_comm]
theorem aB_apply_k (δ : E) (a : AF F) (i k : Fin d.n) :
    aB_k L δ a i k = if i = L.i₀ ∧ k = L.i₀ then a • inclR (AF
      F) δ else 0 := by
  simp [aB_k, single_apply, eq_comm]
variable {R : RD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem frameN_k (h : Hyp_k L nb uM nb' w₁ cM δ) (u b : Fin L.n → AE F
  E) (a : AF F) :
    inFrame d.b (sM_k R L b * cM (u, a)) =
      hN_k L (vV_k L u b + Pi.single (Sum.inr L.i₀) (a • inclR (AF F) δ - hh_k L u b)) (wf_k R L u b) := by
  rw [inFrame_mul, inFrame_sM'_k,
    inFrame_cM_k h,
    bMat_k, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  ext (i | i) (k | k)
  all_goals simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, hN_k, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.add_apply, vV_k,
      wf_k,
    Pi.smul_apply, smul_eq_mul, W_mulVec_inl_k, W_mulVec_inr_k, cv, Sum.elim_inl, Sum.elim_inr]
  · rw [uA_apply_k]
    by_cases hi : i = L.i₀ <;> simp [hi, Matrix.one_apply]
  · rw [aB_apply_k, Matrix.mul_apply, sum_split_k L]
    simp only [D_apply_k]
    rcases idx_k L i with rfl | ⟨p,
      rfl⟩ <;> rcases idx_k L k with rfl | ⟨q, rfl⟩ <;>
      simp [sB_apply_k, extendZeroColumn_apply_embed, extension_by_zero_at_base_index,
        ComplexParameterFamilyContinuity.em_ne_k, (ComplexParameterFamilyContinuity.em_ne_k L _).symm, 
        Matrix.one_apply,
        L.inj.eq_iff, hh_k, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp
  · rw [D_apply_k]
    have he := e_mul_e_k R
    by_cases hk : k = L.i₀ <;> simp [hk, Matrix.one_apply, ← mul_assoc, he]
def cmp_k (L : LD_k d) (M : Mt_k d) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    (Fin L.n → AE F E) × (Fin L.n → AE F E) :=
  (fun k => (vV_k L p.2 p.1 ᵥ* M) (Sum.inr (L.em k)), fun k => (vV_k L p.2 p.1 ᵥ* M) (Sum.inl (L.em k)))
theorem vV_cmp_k {M : Mt_k d} (hM : IsPad_k L M) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    vV_k L p.2 p.1 ᵥ* M = vV_k L (cmp_k L M p).2 (cmp_k L M p).1 := by
  funext r
  rcases r with i | i <;> rcases idx_k L i with rfl | ⟨k, rfl⟩
  · rw [pad_vecMul_inl_k hM]; simp [vV_k, extension_by_zero_at_base_index]
  · simp only [vV_k, cmp_k, Sum.elim_inl, extendZeroColumn_apply_embed]
  · rw [pad_vecMul_inr_k hM]; simp [vV_k, extension_by_zero_at_base_index]
  · simp only [vV_k, cmp_k, Sum.elim_inr, extendZeroColumn_apply_embed]
theorem cmp_cmp_k {J K : Mt_k d} (hK : IsPad_k L K) (hKJ : K * J = 1) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    cmp_k L J (cmp_k L K p) = p := by
  have e := vV_cmp_k hK p
  have e2 : cmp_k L J (cmp_k L K p) = (fun k => (vV_k L (cmp_k L K p).2 (cmp_k L K p).1 ᵥ* J) (Sum.inr (L.em k)),
      fun k => (vV_k L (cmp_k L K p).2 (cmp_k L K p).1 ᵥ* J) (Sum.inl (L.em k))) := rfl
  rw [e2, ← e, Matrix.vecMul_vecMul, hKJ, Matrix.vecMul_one]
  ext k <;> simp [vV_k, extendZeroColumn_apply_embed]
theorem extension_by_zero_add (L : LD_k d) (x y : Fin L.n → AE F E) : extendByZeroColumns L (x + y) =
  extendByZeroColumns L x + extendByZeroColumns L y := by
  funext i
  simp [extendByZeroColumns, mul_add, sum_add_distrib]
theorem vV_add_k (u b u' b' : Fin L.n → AE F E) : vV_k L (u + u') (b + b') = vV_k L u b + vV_k L u' b' := by
  funext r
  rcases r with i | i <;> simp [vV_k, extension_by_zero_add]
section
variable (L : LD_k d)
theorem cmp_add_k (M : Mt_k d) (p q : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    cmp_k L M (p + q) = cmp_k L M p + cmp_k L M q := by
  ext k <;> simp [cmp_k, vV_add_k, Matrix.add_vecMul]
theorem continuous_extension_by_zero (i : Fin d.n) : Continuous fun x : Fin L.n → AE F E =>
  extendByZeroColumns L x i := by
  unfold extendByZeroColumns
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)
theorem continuous_vV_k (r : Fin d.n ⊕ Fin d.n) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => vV_k L p.2 p.1 r := by
  rcases r with i | i
  · exact (continuous_extension_by_zero L i).comp continuous_snd
  · exact (continuous_extension_by_zero L i).comp continuous_fst
theorem continuous_vVM_k (M : Mt_k d) (s : Fin d.n ⊕ Fin d.n) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => (vV_k L p.2 p.1 ᵥ* M) s := by
  simp only [Matrix.vecMul, dotProduct]
  exact continuous_finsetSum _ fun r _ => (continuous_vV_k L r).mul continuous_const
theorem continuous_cmp_k (M : Mt_k d) : Continuous (cmp_k L M) :=
  (continuous_pi fun _ => continuous_vVM_k L M _).prodMk (continuous_pi fun _ => continuous_vVM_k L M _)
end
def cmpEquiv_k (L : LD_k d) {J K : Mt_k d} (hJ : IsPad_k L J) (hK : IsPad_k L K) (hKJ : K * J = 1) (hJK : J * K = 1) :
    ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)) where
  toFun := cmp_k L K
  invFun := cmp_k L J
  left_inv p := cmp_cmp_k hK hKJ p
  right_inv p := cmp_cmp_k hJ hJK p
  map_add' p q := cmp_add_k L K p q
  continuous_toFun := continuous_cmp_k L K
  continuous_invFun := continuous_cmp_k L J
section
variable (L : LD_k d)
theorem Kmul_k (γ' : G2 σ L.Y) : inFrame d.b (L.j γ')⁻¹ * inFrame d.b (L.j γ') = 1 := by
  rw [← inFrame_mul, inv_mul_cancel,
    inFrame_one]
theorem Jmul_k (γ' : G2 σ L.Y) : inFrame d.b (L.j γ') * inFrame d.b (L.j γ')⁻¹ = 1 := by
  rw [← inFrame_mul, mul_inv_cancel,
    inFrame_one]
theorem isPad_inv_k (γ' : G2 σ L.Y) : IsPad_k L (inFrame d.b (L.j γ')⁻¹) := by
  rw [← map_inv]; exact isPad_j_k L _
end
section
variable (R : RD_k d)
theorem K_law_k (L : LD_k d) (γ' : G2 σ L.Y) :
    (inFrame d.b (L.j γ')⁻¹)ᵀ * W_k R * (inFrame d.b (L.j γ')⁻¹).map (cA σ) = W_k R :=
  kunf.frame_eq R.hε _
theorem KWK_k (L : LD_k d) (γ' : G2 σ L.Y) :
    inFrame d.b (L.j γ')⁻¹ * W_k R * ((inFrame d.b (L.j γ')⁻¹).map (cA σ))ᵀ = W_k R := by
  rw [Matrix.mul_assoc, ← JW_k (Kmul_k L γ') (K_law_k R L γ'), ← Matrix.mul_assoc, Kmul_k, Matrix.one_mul]
theorem qf_vV_k (u b : Fin L.n → AE F E) :
    qf_k R (vV_k L u b) = cA σ (hh_k L u b) + ((R.ε : ℤ) : AE F E) * hh_k L u b := by
  simp only [qf_k, dotProduct, Fintype.sum_sum_type, W_mulVec_inl_k, W_mulVec_inr_k, cv, vV_k, Sum.elim_inl,
    Sum.elim_inr]
  rw [sum_split_k L,
    sum_split_k L]

  simp only [extension_by_zero_at_base_index, extendZeroColumn_apply_embed, map_zero, mul_zero, zero_add,
    hh_k, map_sum, map_mul, cc_k d, Finset.mul_sum]
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring
end
def QQ_k (L : LD_k d) (δ : E) (M : Mt_k d) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) : AF F :=
  ellA δ (hh_k L (cmp_k L M p).2 (cmp_k L M p).1 - hh_k L p.2 p.1)
theorem continuous_hh_k (L : LD_k d) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => hh_k L p.2 p.1 := by
  unfold hh_k
  exact continuous_finsetSum _ fun j _ => ((continuous_apply j).comp continuous_fst).mul
    ((continuous_cA σ).comp ((continuous_apply j).comp continuous_snd))
theorem continuous_QQ_k (L : LD_k d) (δ : E) (M : Mt_k d) : Continuous (QQ_k L δ M) := by
  have hl : Continuous (ellA (F := F) δ) := IsModuleTopology.continuous_of_linearMap _
  have h1 : Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => hh_k L (cmp_k L M p).2 (cmp_k L M p).1 :=
    (continuous_hh_k L).comp (continuous_cmp_k L M)
  exact hl.comp (h1.sub (continuous_hh_k L))
theorem conj_eq_k (h : Hyp_k L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) (b u
  : Fin L.n → AE F E) (a : AF F) :
    L.j γ' * (sM_k R L b * cM (u, a)) =
      sM_k R L (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 *
        cM ((cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2, a + QQ_k L δ (inFrame d.b (L.j γ')⁻¹) (b, u)) * L.j γ' := by
  have hK := isPad_inv_k L γ'
  have hJ : IsPad_k L (inFrame d.b (L.j γ')) := isPad_j_k L γ'
  have hKJ := Kmul_k L γ'
  have eV : vV_k L u b ᵥ* inFrame d.b (L.j γ')⁻¹ =
      vV_k L (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 := vV_cmp_k hK (b,
        u)
  have hq : qf_k R (vV_k L (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1) =
      qf_k R (vV_k L u b) := by
    rw [← eV]; exact qf_vecMul_k (KWK_k R L γ') _
  rw [qf_vV_k, qf_vV_k] at hq
  have hy : cA σ (hh_k L (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b,
    u)).1 - hh_k L u b) =
      -(((R.ε : ℤ) : AE F E)) *
        (hh_k L (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp_k L (inFrame d.b (L.j γ')⁻¹) (b,
          u)).1 - hh_k L u b) := by
    rw [map_sub]; linear_combination hq
  have hQ := eig_k h _ hy
  apply kunf.inFrame_injective d.b
  rw [inFrame_mul d.b (L.j γ')
    (sM_k R L b * cM (u, a)),
    inFrame_mul d.b _ (L.j γ'),
    frameN_k h, frameN_k h, conj_hN_k hKJ hJ]
  congr 2
  · rw [Matrix.add_vecMul, eV, pad_single_vecMul_k hK]
    congr 2
    rw [QQ_k, add_smul, hQ]
    ring
  · simp only [wf_k, Matrix.mulVec_smul, mulVec_mulVec]
    rw [JW_k hKJ (K_law_k R L γ'), ← mulVec_mulVec, ← cv_vecMul_k, eV]
section
variable (L : LD_k d)
theorem mem_ratV_iff_k (x : Fin L.n → AE F E) :
    x ∈ L.ratV ↔ ∀ k, x k ∈ (inclR (AF F)).range := by
  constructor
  · intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨z, rfl⟩ := hy; exact fun k => ⟨z k, rfl⟩
    | zero => exact fun k => zero_mem _
    | add y z _ _ hy hz => exact fun k => add_mem (hy k) (hz k)
    | neg y _ hy => exact fun k => neg_mem (hy k)
  · intro hx
    refine AddSubgroup.subset_closure ⟨fun k => (RingHom.mem_range.1 (hx k)).choose, funext fun k => ?_⟩
    exact (RingHom.mem_range.1 (hx k)).choose_spec
theorem index_cases_sum (r : Fin d.n ⊕ Fin d.n) :
    r = Sum.inl L.i₀ ∨ r = Sum.inr L.i₀ ∨ ∃ p, r = Sum.map L.em L.em p := by
  rcases r with i | i <;> rcases idx_k L i with rfl | ⟨p, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨Sum.inl p, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨Sum.inr p, rfl⟩)
theorem j_em_k (g : G2 σ L.Y) (p q : Fin L.n ⊕ Fin L.n) :
    inFrame d.b (L.j g) (Sum.map L.em L.em p) (Sum.map L.em L.em q) = inFrame L.b g p q := by
  have := congrFun (congrFun (L.j_in g) p) q
  simpa [Matrix.submatrix_apply] using this
theorem j_entries_rat_k {g : G2 σ L.Y} (hg : g ∈ rat2 σ L.Y) (r s : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (L.j g) r s ∈ (inclR (AF F)).range := by
  have hP := isPad_j_k L g
  have hone : ∀ r s, (1 : Mt_k d) r s ∈ (inclR (AF F)).range := fun r s => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rcases index_cases_sum L r with rfl | rfl | ⟨p, rfl⟩
  · rw [(hP _ (by simp) s).1]; exact hone _ _
  · rw [(hP _ (by simp) s).1]; exact hone _ _
  · rcases index_cases_sum L s with rfl | rfl | ⟨q, rfl⟩
    · rw [(hP _ (by simp) _).2]; exact hone _ _
    · rw [(hP _ (by simp) _).2]; exact hone _ _
    · rw [j_em_k]; exact inFrame_rat_mem L.b hg p q
theorem extension_by_zero_rational {x : Fin L.n → AE F E} (hx : ∀ k,
  x k ∈ (inclR (AF F)).range)
    (i : Fin d.n) : extendByZeroColumns L x i ∈ (inclR (AF F)).range := by
  unfold extendByZeroColumns
  refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (hx k)
  split_ifs
  · exact one_mem _
  · exact zero_mem _
end
theorem cmp_rat_k {M : Mt_k d} (hM : ∀ r s, M r s ∈ (inclR (F := F) (E := E) (AF F)).range)
    {p : (Fin L.n → AE F E) × (Fin L.n → AE F E)} (hp1 : ∀ k, p.1 k ∈ (inclR (AF F)).range)
    (hp2 : ∀ k, p.2 k ∈ (inclR (AF F)).range) :
    (∀ k, (cmp_k L M p).1 k ∈ (inclR (AF F)).range) ∧
      ∀ k, (cmp_k L M p).2 k ∈ (inclR (AF F)).range := by
  have hv : ∀ r, vV_k L p.2 p.1 r ∈ (inclR (AF F)).range := by
    rintro (i | i)
    · exact extension_by_zero_rational L hp2 i
    · exact extension_by_zero_rational L hp1 i
  have hs : ∀ s, (vV_k L p.2 p.1 ᵥ* M) s ∈ (inclR (AF F)).range := fun s => by
    simp only [Matrix.vecMul, dotProduct]
    exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (hv r) (hM r s)
  exact ⟨fun k => hs _, fun k => hs _⟩
theorem cmpEquiv_apply_k (L : LD_k d) {J K : Mt_k d} (hJ : IsPad_k L J) (hK : IsPad_k L K) (hKJ : K * J = 1) (hJK : J *
  K = 1)
    (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) : cmpEquiv_k L hJ hK hKJ hJK p = cmp_k L K p := rfl
theorem vV_vecMul_apply_k (M : Mt_k d) (u b : Fin L.n → AE F E) (s : Fin d.n ⊕ Fin d.n) :
    (vV_k L u b ᵥ* M) s = ∑ k, u k * M (Sum.inl (L.em k)) s + ∑ k, b k * M (Sum.inr (L.em k)) s := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, vV_k, Sum.elim_inl, Sum.elim_inr]
  rw [sum_split_k L,
    sum_split_k L]
  simp [extension_by_zero_at_base_index, extendZeroColumn_apply_embed]
end PositivityTheory.SiegelWeilFormula.Act.C5.JC
namespace PositivityTheory.SiegelWeilFormula.Act.C5
open JC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem j_conj'_k (h : Hyp_k L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) :
    ∃ (Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)))
      (Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F), Continuous Q ∧
      (∀ b u a, L.j γ' * (sM_k R L b * cM (u, a)) = sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ') ∧
      (γ' ∈ rat2 σ L.Y → ∀ w,
        w ∈ (L.ratV.prod L.ratV : AddSubgroup _) ↔ Λ w ∈ (L.ratV.prod L.ratV : AddSubgroup _)) := by
  refine ⟨JC.cmpEquiv_k L (JC.isPad_j_k L γ') (JC.isPad_inv_k L γ') (JC.Kmul_k L γ') (JC.Jmul_k L γ'),
    JC.QQ_k L δ (inFrame d.b (L.j γ')⁻¹),
    JC.continuous_QQ_k L δ _, fun b u a => JC.conj_eq_k h γ' b u a, fun hr w => ?_⟩
  have hK : ∀ r s, inFrame d.b (L.j γ')⁻¹ r s ∈ (inclR (AF F)).range := fun r s => by
    have := JC.j_entries_rat_k L (inv_mem hr) r s
    rwa [map_inv] at this
  have hJ := JC.j_entries_rat_k L hr
  rw [JC.cmpEquiv_apply_k, AddSubgroup.mem_prod, AddSubgroup.mem_prod, JC.mem_ratV_iff_k, JC.mem_ratV_iff_k,
    JC.mem_ratV_iff_k,
    JC.mem_ratV_iff_k]
  constructor
  · rintro ⟨h1, h2⟩
    exact JC.cmp_rat_k hK h1 h2
  · rintro ⟨h1, h2⟩
    have := JC.cmp_rat_k hJ h1 h2
    rwa [JC.cmp_cmp_k (JC.isPad_inv_k L γ') (JC.Kmul_k L γ')] at this
theorem j_move'_k (h : Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) :
    ∃ (B : Fin L.n → AE F E) (A : AF F), ∀ b a, L.j (nb' β'') * (sM_k R L b * cM (u, a)) =
      sM_k R L (b + B) * cM (u, a + A) * L.j (nb' β'') := by
  have hK : inFrame d.b (L.j (nb' β''))⁻¹ = inFrame d.b (L.j (nb' (-β''))) := by
    rw [kunf.nb_neg h.nb' β'', map_inv]
  have hfr : inFrame L.b (nb' (-β'')) = fromBlocks 1 (-β''.1) 0 1 := by
    rw [h.nb' (-β'')]; rfl
  have k11 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inl (L.em p)) (Sum.inl (L.em q)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) p q := fun p q => by
    have := JC.j_em_k L (nb' (-β'')) (Sum.inl p) (Sum.inl q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k21 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inr (L.em p)) (Sum.inl (L.em q)) = 0 := fun p q => by
    have := JC.j_em_k L (nb' (-β'')) (Sum.inr p) (Sum.inl q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k12 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inl (L.em p)) (Sum.inr (L.em q)) = -β''.1 p q := fun p q => by
    have := JC.j_em_k L (nb' (-β'')) (Sum.inl p) (Sum.inr q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k22 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inr (L.em p)) (Sum.inr (L.em q)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) p q := fun p q => by
    have := JC.j_em_k L (nb' (-β'')) (Sum.inr p) (Sum.inr q)
    rw [hfr] at this
    rw [hK]; simpa using this
  set B : Fin L.n → AE F E := fun k => -∑ k', u k' * β''.1 k' k with hB
  have hc : ∀ b, JC.cmp_k L (inFrame d.b (L.j (nb' β''))⁻¹) (b, u) = (b + B, u) := fun b => by
    ext k
    · show (JC.vV_k L u b ᵥ* _) (Sum.inr (L.em k)) = b k + B k
      rw [JC.vV_vecMul_apply_k]
      simp only [k12, k22, Matrix.one_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', Finset.mem_univ,
        ite_true, hB, mul_neg, Finset.sum_neg_distrib]
      ring
    · show (JC.vV_k L u b ᵥ* _) (Sum.inl (L.em k)) = u k
      rw [JC.vV_vecMul_apply_k]
      simp only [k11, k21, Matrix.one_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.sum_const_zero, add_zero]
  refine ⟨B, ellA δ (JC.hh_k L u B), fun b a => ?_⟩
  have e := JC.conj_eq_k (R := R) h (nb' β'') b u a
  have hQ : JC.QQ_k L δ (inFrame d.b (L.j (nb' β''))⁻¹) (b, u) = ellA δ (JC.hh_k L u B) := by
    rw [JC.QQ_k, hc]
    congr 1
    simp only [JC.hh_k, Pi.add_apply, add_mul, sum_add_distrib]
    ring
  rw [hc, hQ] at e
  exact e
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
