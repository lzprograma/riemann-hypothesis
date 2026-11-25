module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCells
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.ExistsGlCol
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.LagrangianConditionParabolicMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.QE
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.UpperBlockRankOneUpdate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.MemRatVIff

/-! # SiegelWeilAscfourbKey: Consolidated global theta-kernel definitions and proofs (SiegelWeilAscfourbKey). -/
@[expose] public section

noncomputable section
open GlobalTheory.EisBL.DoubledParabolic (inFrame_mul inFrame_one)
open scoped ComplexOrder
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open GlobalTheory.ThK (incV)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section
namespace PositivityTheory.SiegelWeilFormula.Afc
open SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
theorem eps_eq_k {d : SD_k σ} (L :
  LD_k d) {ε ε' : ℤˣ} (hε : FrameEq σ d.Y d.b ε) (hε' : FrameEq σ L.Y L.b ε')
  : ε = ε' := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hnL : 1 ≤ L.n := L.ok.hn
  have key : ∀ (s : ℤ), (∀ i j, σ (d.Y.J j i) = (s : E) * d.Y.J i j) → (∀ i j, σ (L.Y.J j i) = (s : E) * L.Y.J i j) →
      ε = ε' := fun s h1 h2 =>
    Units.ext ((eps_of_sign hσ d.ok.hn hε s h1).trans (eps_of_sign hσ hnL hε' s h2).symm)
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · exact key (-1) (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · exact key 1 (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)

theorem mem_ratV_iff_k {d : SD_k σ} (L :
  LD_k d) (u : Fin L.n → AE F E) :
    u ∈ L.ratV ↔ ∃ v : Fin L.n → E, u = incV F v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ⟨v, rfl⟩
    | zero => exact ⟨0, by funext i; simp [incV]⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨v', rfl⟩ := hy
      exact ⟨v + v', by funext i; simp [incV]⟩
    | neg x _ hx =>
      obtain ⟨v, rfl⟩ := hx
      exact ⟨-v, by funext i; simp [incV]⟩
  · rintro ⟨v, rfl⟩
    exact AddSubgroup.subset_closure ⟨v, rfl⟩
end PositivityTheory.SiegelWeilFormula.Afc
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {d : SD_k σ} (L : LD_k d)
def emS_k : Fin L.n ⊕ Fin L.n → Fin d.n ⊕ Fin d.n := Sum.map L.em L.em
def padM_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fun r c => if h : (∃ a, emS_k L a = r) ∧ ∃ a, emS_k L a = c then M h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r c
theorem emS_inj_k : Function.Injective (emS_k L) := Sum.map_injective.2 ⟨L.inj, L.inj⟩
theorem padM_emS_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (a a' : Fin L.n ⊕ Fin L.n) :
    padM_k L M (emS_k L a) (emS_k L a') = M a a' := by
  have h : (∃ x, emS_k L x = emS_k L a) ∧ ∃ x, emS_k L x = emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [padM_k]
  rw [dite_eq_left h, emS_inj_k L h.1.choose_spec, emS_inj_k L h.2.choose_spec]
theorem padM_out_row_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [padM_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padM_out_col_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, emS_k L a = c) : padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [padM_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem mem_out_k {r : Fin d.n ⊕ Fin d.n} (h : ¬ ∃ a, emS_k L a = r) :
    r ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases r with i | i
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inl a, by simp [emS_k, ha]⟩).elim
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inr a, by simp [emS_k, ha]⟩).elim
theorem em_ne_k (a : Fin L.n) : L.em a ≠ L.i₀ := (L.rng (L.em a)).2 ⟨a, rfl⟩
theorem not_inl_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, emS_k L a = Sum.inl i := by
  rintro ⟨a | a, ha⟩
  · simp only [emS_k, Sum.map_inl, Sum.inl.injEq] at ha
    exact em_ne_k L a (ha.trans hi)
  · simp [emS_k] at ha
theorem not_inr_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, emS_k L a = Sum.inr i := by
  rintro ⟨a | a, ha⟩
  · simp [emS_k] at ha
  · simp only [emS_k, Sum.map_inr, Sum.inr.injEq] at ha
    exact em_ne_k L a (ha.trans hi)
theorem inFrame_j_k (g : G2 σ L.Y) : inFrame d.b (L.j g) = padM_k L (inFrame L.b g) := by
  ext r c
  by_cases h : (∃ a, emS_k L a = r) ∧ ∃ a, emS_k L a = c
  · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := h
    rw [padM_emS_k]
    have := congrFun (congrFun (L.j_in g) a) a'
    simpa [Matrix.submatrix_apply, emS_k] using this
  · rcases not_and_or.1 h with h1 | h1
    · rw [padM_out_row_k L _ h1]
      exact (L.j_out g r (mem_out_k L h1) c).1
    · rw [padM_out_col_k L _ r h1]
      exact (L.j_out g c (mem_out_k L h1) r).2
theorem sub_mem_nA_k (β : nA σ d.Y d.b) : β.1.submatrix L.em L.em ∈ nA σ L.Y L.b := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee := Afc.eps_eq_k L hε hε'
  subst hee
  rw [kunf.mem_nA_iff hε']
  have h1 := (kunf.mem_nA_iff hε β.1).1 β.2
  exact Afc.sub_nCond L.em β.1 h1
def prj_k : nA σ d.Y d.b →+ nA σ L.Y L.b where
  toFun β := ⟨β.1.submatrix L.em L.em, sub_mem_nA_k L β⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' β β' := by
    apply Subtype.ext
    rfl
theorem prj_val_k (β : nA σ d.Y d.b) : (prj_k L β).1 = β.1.submatrix L.em L.em := rfl
theorem continuous_prj_k : Continuous (prj_k L) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtypeVal.matrix_submatrix L.em L.em
theorem pad_matrix_lower_block_zero (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (hM : M.toBlocks₂₁ =
  0) :
    (padM_k L M).toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hi : i = L.i₀
  · rw [padM_out_row_k L M (not_inr_k L i hi)]
    simp
  · by_cases hk : k = L.i₀
    · rw [padM_out_col_k L M _ (not_inl_k L k hk)]
      simp
    · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
      obtain ⟨a', rfl⟩ := (L.rng k).1 hk
      have h1 := padM_emS_k L M (Sum.inr a) (Sum.inl a')
      simp only [emS_k, Sum.map_inr, Sum.map_inl] at h1
      rw [h1]
      have h2 := congrFun (congrFun hM a) a'
      simpa [Matrix.toBlocks₂₁] using h2
theorem embedding_lower_block_zero {x : G2 σ L.Y} (hx : ∃ t, IsPar x t) : (inFrame d.b (L.j x)).toBlocks₂₁ = 0 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨-, t₀, ht₀⟩ := L.ok.frame
  rw [inFrame_j_k]
  exact pad_matrix_lower_block_zero L _ ((kunf.isPar_frame ht₀ x t).1 ht).1
theorem j_par_k {g : G2 σ L.Y} (h : g ∈ par2 σ L.Y) : L.j g ∈ par2 σ d.Y := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
  obtain ⟨-, t₁, ht₁⟩ := d.ok.frame
  set P := inFrame d.b (L.j g)
  set Q := inFrame d.b (L.j g⁻¹)
  have hP : P.toBlocks₂₁ = 0 := embedding_lower_block_zero L ⟨t, ht⟩
  have hQ : Q.toBlocks₂₁ = 0 := embedding_lower_block_zero L ⟨t⁻¹, ht.inv⟩
  have hPQ : P * Q = 1 := by
    rw [← inFrame_mul, ← map_mul, mul_inv_cancel, map_one,
      inFrame_one]
  have hQP : Q * P = 1 := by
    rw [← inFrame_mul, ← map_mul, inv_mul_cancel, map_one,
      inFrame_one]
  have e1 := upper_block_mul_of_lower_zero hQ hPQ
  have e2 := upper_block_mul_of_lower_zero hP hQP
  set T0 := incM F t₁.1
  set Ti := incM F (t₁⁻¹).1
  have hT : T0 * Ti = 1 := by
    show incM F t₁.1 * incM F (t₁⁻¹).1 = 1
    rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
  have hT' : Ti * T0 = 1 := by
    show incM F (t₁⁻¹).1 * incM F t₁.1 = 1
    rw [← kunf.incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]
  let t' : GL (Fin d.n) (AE F E) := ⟨T0 * P.toBlocks₁₁ * Ti, T0 * Q.toBlocks₁₁ * Ti, by
      calc T0 * P.toBlocks₁₁ * Ti * (T0 * Q.toBlocks₁₁ * Ti) = T0 * (P.toBlocks₁₁ * (Ti * T0) * Q.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e1, Matrix.mul_one, hT], by
      calc T0 * Q.toBlocks₁₁ * Ti * (T0 * P.toBlocks₁₁ * Ti) = T0 * (Q.toBlocks₁₁ * (Ti * T0) * P.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e2, Matrix.mul_one, hT]⟩
  exact mem_parabolic_GL2_iff.2 ⟨t', (kunf.isPar_frame ht₁ (L.j g) t').2 ⟨hP, rfl⟩⟩
def padE_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  fun r c => if h : (∃ a, emS_k L a = r) ∧ ∃ a, emS_k L a = c then N h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r c
theorem padM_incM_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : padM_k L (incM F N) = incM F (padE_k L N)
  := by
  ext r c
  simp only [padM_k, padE_k, incM, Matrix.map_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
theorem j_rat_k {g : G2 σ L.Y} (h : g ∈ rat2 σ L.Y) : L.j g ∈ rat2 σ d.Y := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 h
  have hm : mat2 g = incM F γ.1 := by
    show g.1.1 = _
    rw [← hγ]
    rfl
  have hf : inFrame L.b g = incM F ((L.b⁻¹).1 * γ.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]
    rfl
  refine kunf.rat_of_inFrame (b := d.b) (M := padE_k L ((L.b⁻¹).1 * γ.1 * L.b.1)) ?_
  rw [inFrame_j_k, hf, padM_incM_k]
end PositivityTheory.SiegelWeilFormula.Act.C4
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {d : SD_k σ} (L : LD_k d)
namespace Bq
open Matrix
theorem padE_emS_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (a a' : Fin L.n ⊕ Fin L.n) :
    padE_k L N (emS_k L a) (emS_k L a') = N a a' := by
  have h : (∃ x, emS_k L x = emS_k L a) ∧ ∃ x, emS_k L x = emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [padE_k]
  rw [dite_eq_left h, emS_inj_k L h.1.choose_spec, emS_inj_k L h.2.choose_spec]
theorem padE_out_row_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [padE_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padE_out_col_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, emS_k L a = c) : padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [padE_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem nq_E_k {M : Matrix d.N2 d.N2 E}
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix d.N2 d.N2 E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0)
    {H' : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E} (hH : M.submatrix (emS_k L) (emS_k L) * H' = 1) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (M * padE_k L H') := by
  have hxo := not_inl_k L L.i₀ rfl
  have hyo := not_inr_k L L.i₀ rfl
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · have : (M * padE_k L H') k (Sum.inl L.i₀) = (M * (1 : Matrix d.N2 d.N2 E)) k
        (Sum.inl L.i₀) := by
      simp only [Matrix.mul_apply, padE_out_col_k L H' _ hxo]
    rw [Matrix.sub_apply, this, Matrix.mul_one, hx k, sub_self]
  · have hl : ∃ c', emS_k L c' = l := by
      by_contra hc
      rcases mem_out_k L hc with h | h
      · exact hlx h
      · exact hly h
    obtain ⟨c', rfl⟩ := hl
    have hsum : (M * padE_k L H') k (emS_k L c') = ∑ a', M k (emS_k L a') * H' a' c' := by
      rw [Matrix.mul_apply, sum_emb (emS_k L) (emS_inj_k L)]
      · simp only [padE_emS_k]
      · intro m hm
        rw [padE_out_row_k L H' (fun h => hm (by obtain ⟨a, ha⟩ := h; exact ⟨a, ha⟩)), Matrix.one_apply_ne, mul_zero]
        rintro rfl
        exact hm ⟨c', rfl⟩
    rw [Matrix.sub_apply, hsum]
    by_cases hk : ∃ a, emS_k L a = k
    · obtain ⟨a, rfl⟩ := hk
      have := congrFun (congrFun hH a) c'
      rw [Matrix.mul_apply] at this
      simp only [Matrix.submatrix_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp [(emS_inj_k L).eq_iff]
    · rcases mem_out_k L hk with h | h
      · exact (hkx h).elim
      · have h' := h
        subst h'
        rw [Finset.sum_eq_zero fun a' _ => by rw [hy _ (fun he => hyo ⟨a', he⟩), zero_mul], Matrix.one_apply_ne,
            sub_self]
        intro he
        exact hyo ⟨c', he.symm⟩
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end

section
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {d : SD_k σ} (L : LD_k d)
namespace Bq
theorem blockH_form_k {ε : ℤˣ} {M : Matrix d.N2 d.N2 E}
    (hM : Mᵀ * QE d.n ε * M.map σ = QE d.n ε)
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix d.N2 d.N2 E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0) :
    (M.submatrix (emS_k L) (emS_k L))ᵀ * QE L.n ε * (M.submatrix (emS_k L) (emS_k L)).map σ = QE L.n ε := by
  have hQx : ∀ r, r ≠ Sum.inr L.i₀ → QE (E := E) d.n ε r (Sum.inl L.i₀) = 0 := by
    intro r hr
    rcases r with i | i
    · simp [QE]
    · have hi : i ≠ L.i₀ := fun h => hr (by rw [h])
      simp [QE, Matrix.one_apply, hi]
  have hQx' : ∀ a', QE (E := E) d.n ε (Sum.inl L.i₀) (emS_k L a') = 0 := by
    intro a'
    rcases a' with k | k
    · simp [QE, emS_k]
    · simp [QE, emS_k, Matrix.one_apply, Ne.symm (em_ne_k L k)]
  have hne : ∀ a', emS_k L a' ≠ Sum.inr L.i₀ := by
    intro a'
    rcases a' with k | k
    · simp [emS_k]
    · simp [emS_k, em_ne_k L k]
  have hQQ : ∀ a' c', QE (E := E) d.n ε (emS_k L a') (emS_k L c') = QE L.n ε a' c' := by
    intro a' c'
    rcases a' with k | k <;> rcases c' with k' | k' <;> simp [QE, emS_k, Matrix.one_apply, L.inj.eq_iff]
  refine Matrix.ext fun a c => ?_
  have h := congrFun (congrFun hM (emS_k L a)) (emS_k L c)
  rw [← hQQ, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Finset.sum_mul]
  symm
  rw [Bq.sum_emb (emS_k L) (emS_inj_k L)]
  · refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Bq.sum_emb (emS_k L) (emS_inj_k L)]
    · exact Finset.sum_congr rfl fun a' _ => by rw [hQQ]
    · intro r hr
      have hm := mem_out_k L hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl
      · rw [hQx', mul_zero, zero_mul]
      · rw [hy _ (hne a), zero_mul, zero_mul]
  · intro s hs
    have hm := mem_out_k L hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = Sum.inr L.i₀
      · subst hr
        rw [hy _ (hne a), zero_mul, zero_mul]
      · rw [hQx r hr, mul_zero, zero_mul]
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [hy _ (hne c), map_zero, mul_zero]
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end

section
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {d : SD_k σ} (L : LD_k d)
namespace Bq
section
variable {d : SD_k σ}
section
variable (L : LD_k d)
theorem inStabilizer_parabolic_mul {p γ : d.G} (hp : p ∈ d.p2)
                        (hγ : Act.FirstOrbit L γ) : Act.FirstOrbit L (p * γ) := by
  intro i
  have hP := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p).1 hp
  have e1 : ∀ j, inFrame d.b p (Sum.inr i) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP i) j
    simpa [Matrix.toBlocks₂₁] using this
  rw [inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [e1, hγ _]
theorem inStabilizer_smallerGroupEmbed (g : G2 σ L.Y) : Act.FirstOrbit L (L.j g) := by
  intro i
  exact (L.j_out g (Sum.inl L.i₀) (by simp) (Sum.inr i)).2.trans (by simp [Matrix.one_apply])
theorem par_of_j_k {g : G2 σ L.Y} (h : L.j g ∈ d.p2) : g ∈ par2 σ L.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame, inFrame_j_k] at h
  refine Matrix.ext fun a c => ?_
  have h1 := congrFun (congrFun h (L.em a)) (L.em c)
  have h2 := padM_emS_k L (inFrame L.b g) (Sum.inr a) (Sum.inl c)
  simp only [emS_k, Sum.map_inr, Sum.map_inl] at h2
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at h1 ⊢
  rw [← h2]
  exact h1
end
end
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end

section
open Matrix (GeneralLinearGroup det_mul fromBlocks)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {d : SD_k σ} (L : LD_k d)
namespace Bq
theorem pad_j_k (g : G2 σ L.Y) : Pad (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (L.j g)) := by
  intro r c h
  rcases h with h | h | h | h
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g c (by simp [h]) r).2
  · exact (L.j_out g c (by simp [h]) r).2
def bp_k (β : d.Mn) : d.Mn :=
  Matrix.of fun i k => if i = L.i₀ ∨ k = L.i₀ then 0 else β i k
theorem padM_n_k (β : d.Mn) :
    padM_k L (fromBlocks 1 (-(β.submatrix L.em L.em)) 0 1) = fromBlocks 1 (-(bp_k L β)) 0 1 := by
  refine Matrix.ext fun r c => ?_
  rcases r with i | i <;> rcases c with k | k
  all_goals
    by_cases hi : i = L.i₀
    · first
        | rw [padM_out_row_k L _ (not_inl_k L i hi)]
        | rw [padM_out_row_k L _ (not_inr_k L i hi)]
      subst hi
      simp [bp_k, Matrix.one_apply]
    · by_cases hk : k = L.i₀
      · first
          | rw [padM_out_col_k L _ _ (not_inl_k L k hk)]
          | rw [padM_out_col_k L _ _ (not_inr_k L k hk)]
        subst hk
        simp [bp_k, Matrix.one_apply, hi]
      · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
        obtain ⟨a', rfl⟩ := (L.rng k).1 hk
        first
          | exact (padM_emS_k L _ (Sum.inl a) (Sum.inl a')).trans (by simp [bp_k, Matrix.one_apply, L.inj.eq_iff,
              em_ne_k])
          | exact (padM_emS_k L _ (Sum.inl a) (Sum.inr a')).trans (by simp [bp_k, Matrix.one_apply, L.inj.eq_iff,
              em_ne_k])
          | exact (padM_emS_k L _ (Sum.inr a) (Sum.inl a')).trans (by simp [bp_k, Matrix.one_apply, L.inj.eq_iff,
              em_ne_k])
          | exact (padM_emS_k L _ (Sum.inr a) (Sum.inr a')).trans (by simp [bp_k, Matrix.one_apply, L.inj.eq_iff,
              em_ne_k])
theorem unipotentEntry_eq_zero (u : Fin L.n → AE F E) (a k : Fin d.n) (h : a ≠ L.i₀ ∨ k =
    L.i₀) : Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u a k = 0 := by
  simp only [Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.single_apply_of_ne]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h h1.symm
  · exact em_ne_k L j (h2.trans h)
theorem nq_q_k (β : d.Mn) (u : Fin L.n → AE F E) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀)
      (fromBlocks 1 β 0 1 * Act.ComplexParameterFamilyContinuity.muF_k L u * fromBlocks 1
          (-(bp_k L β)) 0 1) := by
  set A := 1 + Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u with hA
  set D := ((1 - Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ) with hD
  have e : fromBlocks 1 β 0 1 * Act.ComplexParameterFamilyContinuity.muF_k L u * fromBlocks 1
      (-(bp_k L β)) 0 1 =
      fromBlocks A (-(A * bp_k L β) + β * D) 0 D := by
    simp only [Act.ComplexParameterFamilyContinuity.muF_k, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
        Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_neg, hA, hD]
    congr 1
    abel
  have hA1 : ∀ a k, a ≠ L.i₀ ∨ k = L.i₀ → (A - 1) a k = 0 := fun a k h => by
    rw [hA, add_sub_cancel_left, unipotentEntry_eq_zero L u a k h]
  have hD1 : ∀ a k, k ≠ L.i₀ → D a k = (1 : Matrix _ _ (AE F E)) a k := fun a k hk => by
    simp only [hD, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, unipotentEntry_eq_zero L u k a
        (Or.inl hk), sub_zero]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : k = a
    · subst h; simp [map_one]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), map_zero]
  rw [e]
  refine Bq.NQ.of_blocks (fun a => hA1 a L.i₀ (Or.inr rfl)) (fun a k ha => hA1 a k (Or.inl ha)) (fun a k ha hk => ?_)
    (fun a k hk => by rw [Matrix.sub_apply, hD1 a k hk, sub_self])
  have h1 : (A * bp_k L β) a k = β a k := by
    rw [Matrix.mul_apply]
    have : ∀ m, A a m * bp_k L β m k = if m = a then β a k else 0 := fun m => by
      have hAm : A a m = (1 : Matrix _ _ (AE F E)) a m := by
        have := hA1 a m (Or.inl ha); rwa [Matrix.sub_apply, sub_eq_zero] at this
      rw [hAm, Matrix.one_apply]
      by_cases hm : a = m
      · subst hm; simp [bp_k, ha, hk]
      · simp [hm, Ne.symm hm]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h2 : (β * D) a k = β a k := by
    rw [Matrix.mul_apply]
    simp only [hD1 _ k hk, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.add_apply, Matrix.neg_apply, h1, h2, neg_add_cancel]
theorem isPar_of_nq_k {p : d.G} (h : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p)) :
    ∃ t, IsPar p t ∧ GeneralLinearGroup.det t = 1 := by
  obtain ⟨-, t₀, ht₀⟩ := d.ok.frame
  set M := inFrame d.b p
  set T0 := incM F t₀.1
  set T0i := incM F (t₀⁻¹).1
  have e1 : T0 * T0i = 1 := by
    simp only [T0, T0i, incM, ← Matrix.map_mul]
    rw [show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdet : (T0 * M.toBlocks₁₁ * T0i).det = 1 := by
    rw [det_mul, det_mul, h.upper_block_det_one, mul_one, ← det_mul, e1, Matrix.det_one]
  have hu : IsUnit (T0 * M.toBlocks₁₁ * T0i) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, (kunf.isPar_frame ht₀ p hu.unit).2 ⟨h.projected_block_lower_sum, rfl⟩, ?_⟩
  ext
  simp [GeneralLinearGroup.val_det_apply, hdet]
end Bq
theorem key_id_pf_k {nb : d.nA_ → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : d.nA_) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (prj_k L β)) * x) := by
  set q := nb β * uM u * L.j (nb' (-prj_k L β)) with hq
  set p := L.j h * q * L.j h⁻¹ with hp
  have hinv : L.j (nb' (-prj_k L β)) = (L.j (nb' (prj_k L β)))⁻¹ := by
    rw [kunf.nb_neg hnb', map_inv]
  have hid : L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (prj_k L β)) * x) := by
    simp only [hp, hq, hinv, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have hQ : inFrame d.b q = fromBlocks 1 β.1 0 1 * Act.ComplexParameterFamilyContinuity.muF_k L u *
      fromBlocks 1 (-(Bq.bp_k L β.1)) 0 1 := by
    rw [hq, inFrame_mul, inFrame_mul, hnb β,
        Act.ComplexParameterFamilyContinuity.inFrame_uM_k L hU u, inFrame_j_k,
      hnb' (-prj_k L β), ← Bq.padM_n_k L β.1]
    rfl
  have hJJ : inFrame d.b (L.j h) * inFrame d.b (L.j h⁻¹) = 1 := by
    rw [← inFrame_mul, ← map_mul, mul_inv_cancel, map_one,
        inFrame_one]
  have hnq : Bq.NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p) := by
    rw [hp, inFrame_mul, inFrame_mul, hQ]
    exact Bq.NQ.conj (by simp) (Bq.pad_j_k L h) (Bq.pad_j_k L h⁻¹) hJJ (Bq.nq_q_k L β.1 u)
  obtain ⟨t, ht, hdt⟩ := Bq.isPar_of_nq_k L hnq
  exact ⟨p, t, ht, hdt, hid⟩
end PositivityTheory.SiegelWeilFormula.Act.C4
end

section
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {d : SD_k σ} (L : LD_k d)
namespace Bq
theorem surj_k {γ : d.G} (hγ : γ ∈ d.r2) (hS : Act.FirstOrbit L γ) :
    ∃ p ∈ d.p2, p ∈ d.r2 ∧ ∃ g ∈ rat2 σ L.Y, γ = p * L.j g := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  obtain ⟨G0', hG0'⟩ := Afc.rat_frame (b := d.b) γ⁻¹ (inv_mem hγ)
  have hGG : G0' * G0 = 1 := kfour.incM_injective (F := F) (by
    rw [kfour.incM_mul', ← hG0, ← hG0', ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel,
        GlobalTheory.EisBL.DoubledParabolic.inFrame_one,
      Afc.incM_one'])
  have hS0 : ∀ i, G0 (Sum.inr i) (Sum.inl L.i₀) = 0 := fun i => by
    have h1 := hS i
    rw [hG0] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  set v : Fin d.n → E := fun k => G0 (Sum.inl k) (Sum.inl L.i₀) with hv_def
  have hv : v ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun hGG (Sum.inl L.i₀)) (Sum.inl L.i₀)
    have h2 : ∀ k, G0 (Sum.inl k) (Sum.inl L.i₀) = 0 := fun k => congrFun h0 k
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h1
    simp only [h2, hS0, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  obtain ⟨a, ha⟩ := exists_gl_col L.i₀ v hv
  obtain ⟨p1, hp1r, hp1⟩ := Afc.levi_ex hσ d.ok.frame a⁻¹
  have hp1P : p1 ∈ d.p2 :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p1).2 (by rw [hp1,
        Matrix.toBlocks_fromBlocks₂₁])
  set P1 : Matrix d.N2 d.N2 E :=
    Matrix.fromBlocks (a⁻¹).1 0 0 ((((a⁻¹)⁻¹).1)ᵀ.map σ) with hP1_def
  have hP1 : inFrame d.b p1 = incM F P1 := by
    rw [hp1, hP1_def, Afc.incM_fromBlocks, show incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 from kfour.incM_zero]
  set M1 := P1 * G0 with hM1_def
  have hM1 : inFrame d.b (p1 * γ) = incM F M1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, hM1_def, kfour.incM_mul']
  have hγ1 : p1 * γ ∈ d.r2 := mul_mem hp1r hγ
  have hx : ∀ r, M1 r (Sum.inl L.i₀) = (1 : Matrix d.N2 d.N2 E) r (Sum.inl L.i₀) := by
    intro r
    rw [hM1_def, Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | i
    · simp only [hP1_def, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero]
      have e1 : ∀ j, G0 (Sum.inl j) (Sum.inl L.i₀) = a.1 j L.i₀ := fun j => (ha j).symm
      simp only [e1]
      rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp [Matrix.one_apply]
    · simp [hP1_def, hS0, Matrix.one_apply]
  have hform := form_E hε (p1 * γ) hM1
  have hy := yrow_zero hform hx
  set H := M1.submatrix (emS_k L) (emS_k L) with hH_def
  have hH := blockH_form_k L hform hx hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨h, hh⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hhr : h ∈ rat2 σ L.Y := kunf.rat_of_inFrame hh
  have hh' : inFrame L.b h⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hh]
    exact Matrix.inv_eq_right_inv hIA
  have hnF : inFrame d.b (p1 * γ * L.j h⁻¹) = incM F (M1 * padE_k L H') := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0,
        inFrame_j_k, hh', padM_incM_k, hM1_def,
      kfour.incM_mul', kfour.incM_mul']
  have hnq : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (p1 * γ * L.j h⁻¹)) := by
    rw [hnF]
    exact NQ.map _ (nq_E_k L hx hy hHH')
  have hnP : p1 * γ * L.j h⁻¹ ∈ d.p2 :=
      (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2
      hnq.projected_block_lower_sum
  have hnR := mul_mem hγ1 (j_rat_k L (inv_mem hhr))
  refine ⟨p1⁻¹ * (p1 * γ * L.j h⁻¹), mul_mem (inv_mem hp1P) hnP, mul_mem (inv_mem hp1r) hnR, h, hhr, ?_⟩
  rw [map_inv]
  group
theorem rep_mk_k {d : SD_k σ} (x : d.r2) :
    ∃ p ∈ d.p2, p ∈ d.r2 ∧ Act.rep_k (GlobalTheory.AutomorphicL2Unitary.mk (d.p2.subgroupOf
        d.r2) x) = p * x := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
    (Quotient.out_eq (GlobalTheory.AutomorphicL2Unitary.mk (d.p2.subgroupOf d.r2) x)).symm
  refine ⟨((γ : d.r2) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : d.r2).2, ?_⟩
  show (((Quotient.out (GlobalTheory.AutomorphicL2Unitary.mk (d.p2.subgroupOf
      d.r2) x)) : d.r2) : d.G) = _
  rw [← hγ]
  rfl
end Bq
theorem cos_bij_pf_k : ∃ e : Act.Cs_k L.sd ≃ {q : Act.Cs_k d // Act.FirstOrbit L (Act.rep_k q)}, ∀ q', ∃ p ∈ d.p2,
    p ∈ d.r2 ∧
    Act.rep_k (e q').1 = p * L.j (Act.rep_k q') := by
  set H := d.p2.subgroupOf d.r2 with hH
  set H' := (par2 σ L.Y).subgroupOf (rat2 σ L.Y) with hH'
  let jr : rat2 σ L.Y → d.r2 := fun γ => ⟨L.j γ, j_rat_k L γ.2⟩
  let e0 : Act.Cs_k L.sd → Act.Cs_k d := Quotient.lift (fun γ => GlobalTheory.AutomorphicL2Unitary.mk H (jr γ)) (by
    intro a b hab
    have hab' : b * a⁻¹ ∈ H' := QuotientGroup.rightRel_apply.1 hab
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨jr (b * a⁻¹), ?_⟩, ?_⟩
    · rw [hH', Subgroup.mem_subgroupOf] at hab'
      rw [hH, Subgroup.mem_subgroupOf]
      exact j_par_k L hab'
    · apply Subtype.ext
      show L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) * L.j a = L.j b
      rw [map_mul, map_inv, inv_mul_cancel_right])
  have he0 : ∀ γ, e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ) = GlobalTheory.AutomorphicL2Unitary.mk H (jr γ) :=
      fun γ => rfl
  have hS : ∀ q', Act.FirstOrbit L (Act.rep_k (e0 q')) := by
    intro q'
    induction q' using Quotient.inductionOn with
    | h γ =>
      obtain ⟨p, hp, -, hrep⟩ := Bq.rep_mk_k (jr γ)
      have e1 : Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = p * L.j γ := by rw [he0]; exact hrep
      show Act.FirstOrbit L (Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)))
      rw [e1]
      exact Bq.inStabilizer_parabolic_mul L hp (Bq.inStabilizer_smallerGroupEmbed L γ)
  let e : Act.Cs_k L.sd → {q : Act.Cs_k d // Act.FirstOrbit L (Act.rep_k q)} := fun q' => ⟨e0 q', hS q'⟩
  have hinj : Function.Injective e := by
    intro q1 q2 h12
    have h0 := congrArg Subtype.val h12
    induction q1 using Quotient.inductionOn with
    | h a =>
      induction q2 using Quotient.inductionOn with
      | h b =>
        change GlobalTheory.AutomorphicL2Unitary.mk H (jr a) = GlobalTheory.AutomorphicL2Unitary.mk H (jr b) at h0
        obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h0
        have hγv : ((γ : d.r2) : d.G) = L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) := by
          have := congrArg Subtype.val hγ
          simp only [Subgroup.coe_mul, jr] at this
          rw [map_mul, map_inv, ← this, mul_inv_cancel_right]
        have hP : (b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹ ∈ par2 σ L.Y := by
          apply Bq.par_of_j_k L
          rw [← hγv]
          exact Subgroup.mem_subgroupOf.1 γ.2
        change GlobalTheory.AutomorphicL2Unitary.mk H' a = GlobalTheory.AutomorphicL2Unitary.mk H' b
        rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
        refine ⟨⟨b * a⁻¹, Subgroup.mem_subgroupOf.2 hP⟩, ?_⟩
        simp
  have hsurj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hpP, hpR, g, hg, hγ⟩ := Bq.surj_k L (Quotient.out q).2 hq
    refine ⟨GlobalTheory.AutomorphicL2Unitary.mk H' ⟨g, hg⟩, Subtype.ext ?_⟩
    show GlobalTheory.AutomorphicL2Unitary.mk H (jr ⟨g, hg⟩) = q
    conv_rhs => rw [← Quotient.out_eq q]
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨⟨p, hpR⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
    exact hγ.symm
  refine ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, fun q' => ?_⟩
  induction q' using Quotient.inductionOn with
  | h γ =>
    obtain ⟨p, hpP, hpR, hrep⟩ := Bq.rep_mk_k (jr γ)
    obtain ⟨p', hp'P, hp'R, hrep'⟩ := Bq.rep_mk_k (d := L.sd) γ
    refine ⟨p * L.j p'⁻¹, mul_mem hpP (j_par_k L (inv_mem hp'P)), mul_mem hpR (j_rat_k L (inv_mem hp'R)), ?_⟩
    show Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = _
    rw [he0, hrep, hrep', map_mul, map_inv]
    simp only [jr]
    group
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
