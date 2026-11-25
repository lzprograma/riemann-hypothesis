module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

@[expose] public section

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.LieCovol

theorem exists_transport (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ))
    (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) (R : Type) [Fintype R] (j : ℕ) (r : R ≃ Fin j) :
    ∃ Ψ : (ι → R → ℂ) ≃L[ℝ] (InfinitePlace K → Fin j → ℂ), MeasurePreserving Ψ volume volume ∧
      ∀ x : R → K, Ψ (fun v q => τ v (x q)) = GlobalTheory.LatFacts.emb K j (fun a => x (r.symm a)) := by
  classical
  let e : ι ≃ InfinitePlace K := Equiv.ofBijective _ ⟨fun a b h => (hτ _).unique h rfl, fun w => (hτ w).exists⟩
  let g (w : InfinitePlace K) : ℂ ≃ₗᵢ[ℝ] ℂ := if w.embedding = τ (e.symm w) then .refl ℝ ℂ else Complex.conjLIE
  let Ψl : (ι → R → ℂ) ≃ₗ[ℝ] (InfinitePlace K → Fin j → ℂ) :=
    ((LinearEquiv.funCongrLeft ℝ (R → ℂ) e.symm).trans
      (.piCongrRight fun _ => .funCongrLeft ℝ ℂ r.symm)).trans
      (.piCongrRight fun w => .piCongrRight fun _ => (g w).toLinearEquiv)
  refine ⟨Ψl.toContinuousLinearEquiv, ?_, fun x => funext fun w => funext fun a => ?_⟩
  · have h12 : MeasurePreserving
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.arrowCongr' r (MeasurableEquiv.refl ℂ))) volume volume :=
      volume_preserving_arrowCongr' _ _ (volume_preserving_arrowCongr' _ _ (MeasurePreserving.id _))
    have h3 : MeasurePreserving (fun (y : InfinitePlace K → Fin j → ℂ) w a => g w (y w a)) volume volume :=
      measurePreserving_pi _ _ fun w => measurePreserving_pi _ _ fun _ => (g w).measurePreserving
    convert h3.comp h12 using 1; funext c w a; rfl
  · show g w (τ (e.symm w) (x (r.symm a))) = w.embedding (x (r.symm a))
    by_cases hw : w.embedding = τ (e.symm w)
    · simp [g, hw]
    · simp only [g, hw, ↓reduceIte, Complex.conjLIE_apply]
      have he : InfinitePlace.mk (τ (e.symm w)) = w := e.apply_symm_apply w
      rcases he ▸ InfinitePlace.embedding_mk_eq (τ (e.symm w)) with h | h
      · exact absurd h hw
      · rw [h, ComplexEmbedding.conjugate_coe_eq]

theorem exists_act (ι : Type) [Fintype ι] (R : Type) [Fintype R] [DecidableEq R] (M : ι → Matrix R R ℂ) (hM : ∀ v, (M v).det = 1) :
    ∃ Φ : (ι → R → ℂ) ≃L[ℝ] (ι → R → ℂ), MeasurePreserving Φ volume volume ∧ ∀ c v, Φ c v = M v *ᵥ c v := by
  classical
  let e (v : ι) : (R → ℂ) ≃ₗ[ℝ] (R → ℂ) :=
    (Matrix.toLinearEquiv' (M v) (Matrix.invertibleOfIsUnitDet _ (by rw [hM]; exact isUnit_one))).restrictScalars ℝ
  refine ⟨(LinearEquiv.piCongrRight e).toContinuousLinearEquiv,
    measurePreserving_pi (fun _ => volume) (fun _ => volume) (α := fun _ => R → ℂ)
      (fun v => ?_ : ∀ v, MeasurePreserving (e v) volume volume), fun _ _ => rfl⟩
  have hdet : LinearMap.det (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ)) = 1 := by
    show LinearMap.det ((Matrix.toLin' (M v)).restrictScalars ℝ) = 1
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', hM v, map_one]
  exact ⟨(LinearMap.continuous_of_finiteDimensional (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))).measurable, by
    simpa [hdet] using Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (R → ℂ))
      (f := (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))) (by rw [hdet]; exact one_ne_zero)⟩

theorem vInv_pow_le (K : Type) [Field K] [NumberField K] :
    Formalism.HermitianLatticesTheory.vInv K ^ Formalism.HermitianLatticesTheory.fDeg K ≤ |(discr K : ℝ)| ^ (1 / 2 : ℝ) := by
  have : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    show (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K) * _ = 1 / 2 by field_simp]
  exact div_le_self (Real.rpow_nonneg (abs_nonneg _) _) (one_le_pow₀ (by norm_num))

set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_eq_relIndex_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup * ZLattice.covolume L₂ μ := by
  classical
  let b₂ := Module.Free.chooseBasis ℤ L₂
  have hc : Fintype.card (Free.ChooseBasisIndex ℤ L₁) = Fintype.card (Free.ChooseBasisIndex ℤ L₂) := by
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂]
  let b₁ := (Module.Free.chooseBasis ℤ L₁).reindex (Fintype.equivOfCardEq hc)
  rw [ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ (b₂.ofZLatticeBasis ℝ L₂),
    ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ (b₂.ofZLatticeBasis ℝ L₂),
    show ((↑) ∘ b₂ : _ → E) = b₂.ofZLatticeBasis ℝ L₂ from funext fun _ => by simp,
    Basis.det_self, abs_one, one_mul, AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂]
  congr 1; rw [Nat.cast_natAbs, Int.cast_abs, Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr 2; ext i k; rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ k, h (b₁ k).2⟩ i

theorem exists_domain (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι]
    (τ : ι → (K →+* ℂ)) (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) (R : Type) [Fintype R] [DecidableEq R]
    (H : AddSubgroup (R → 𝓞 K)) (hH : H.index ≠ 0) (M : ι → Matrix R R ℂ) (hM : ∀ v, (M v).det = 1)
    (Λ : Submodule ℤ (ι → R → ℂ))
    (hΛ : ∀ c, c ∈ Λ ↔ ∃ x ∈ H, ∀ v, M v *ᵥ c v = fun q => τ v (x q)) :
    ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ IsAddFundamentalDomain Λ Ω volume ∧
      volume Ω ≤ ENNReal.ofReal (H.index * (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R) := by
  classical
  have : (volume : Measure (ι → R → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set j := Fintype.card R; let r : R ≃ Fin j := Fintype.equivFin R
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_transport K ι τ hτ R j r
  obtain ⟨Φ, hΦ, hΦe⟩ := exists_act ι R M hM
  let T : (ι → R → ℂ) ≃L[ℝ] GlobalTheory.FlagBase.VecInf K j := Φ.trans Ψ
  let f0 : (R → 𝓞 K) →ₗ[ℤ] GlobalTheory.FlagBase.VecInf K j :=
    ((GlobalTheory.LatFacts.emb K j).comp
      (AddMonoidHom.mk' (fun x a => ((x (r.symm a) : 𝓞 K) : K)) fun _ _ => by ext; simp)).toIntLinearMap
  have hf0inj : Function.Injective f0 := fun x y hxy => funext fun q => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    have h1 := congrFun (congrFun hxy w) (r q)
    simp only [f0, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.mk'_apply, GlobalTheory.LatFacts.emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Equiv.symm_apply_apply] at h1
    exact Subtype.val_injective (w.embedding.injective h1)
  let bR := (Pi.basis fun _ : Fin j => RingOfIntegers.basis K).map (LinearEquiv.funCongrLeft ℤ (𝓞 K) r)
  let Lf : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j) := Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.intB K j))
  let LH : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j) := H.toIntSubmodule.map f0
  have hLf : Lf = (⊤ : Submodule ℤ (R → 𝓞 K)).map f0 := by
    have hfb : f0 ∘ bR = GlobalTheory.LatFacts.intB K j := funext fun ⟨a, i⟩ => by
      rw [Function.comp_apply, GlobalTheory.LatFacts.intB_apply]
      show GlobalTheory.LatFacts.emb K j _ = GlobalTheory.LatFacts.emb K j _
      congr 1; funext c
      by_cases hc : c = a <;> simp [bR, GlobalTheory.LatFacts.ratB, Pi.basis_apply, hc, integralBasis_apply]
    rw [← bR.span_eq, Submodule.map_span, ← Set.range_comp, hfb]
  have hle : LH ≤ Lf := hLf ▸ Submodule.map_mono le_top
  have hidx : LH.toAddSubgroup.relIndex Lf.toAddSubgroup = H.index := by
    rw [hLf, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.toIntSubmodule_toAddSubgroup, Submodule.top_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hf0inj, AddSubgroup.relIndex_top_right]
  have hdLf : DiscreteTopology Lf := by dsimp only [Lf]; infer_instance
  have : IsZLattice ℝ Lf := by dsimp only [Lf]; infer_instance
  have : DiscreteTopology LH := DiscreteTopology.of_subset (s := (Lf : Set _)) hdLf hle
  have : IsZLattice ℝ LH := ⟨eq_top_iff.2 <| IsZLattice.span_top (K := ℝ) (L := Lf) ▸ Submodule.span_le.2 fun y hy => by
    have hmem : H.index • y ∈ LH.toAddSubgroup := hidx ▸ AddSubgroup.nsmul_relIndex_mem _ hy
    rw [show y = (H.index : ℝ)⁻¹ • ((H.index : ℝ) • y) by
      rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hH), one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Nat.cast_smul_eq_nsmul ℝ H.index y ▸ hmem))⟩
  have hΛeq : Λ = ZLattice.comap ℝ LH T.toLinearMap := Submodule.ext fun c => by
    rw [hΛ]; change _ ↔ Ψ (Φ c) ∈ LH
    rw [Submodule.mem_map, show Φ c = fun v => M v *ᵥ c v from funext (hΦe c)]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    change _ ↔ GlobalTheory.LatFacts.emb K j (fun a => ((x (r.symm a) : 𝓞 K) : K)) = _
    rw [← hΨe (fun q => ((x q : 𝓞 K) : K)), Ψ.injective.eq_iff, eq_comm, funext_iff]
  subst hΛeq
  let b := Module.Free.chooseBasis ℤ (ZLattice.comap ℝ LH T.toLinearMap)
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _,
    ZLattice.isAddFundamentalDomain b volume, ?_⟩
  rw [← ofReal_measureReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne,
    ← ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZLattice.isAddFundamentalDomain b volume),
    ZLattice.covolume_comap LH volume volume (hΨ.comp hΦ : MeasurePreserving T volume volume),
    covolume_eq_relIndex_mul volume LH Lf hle, hidx,
    ZLattice.covolume_eq_measure_fundamentalDomain Lf volume
      (ZSpan.isAddFundamentalDomain (GlobalTheory.LatFacts.intB K j) volume),
    GlobalTheory.LatFacts.volume_fd_intB K j, pow_mul]
  exact ENNReal.ofReal_le_ofReal <| mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by unfold Formalism.HermitianLatticesTheory.vInv; positivity) (vInv_pow_le K) _)
    (Nat.cast_nonneg _)

theorem index_le (K : Type) [Field K] [NumberField K] (R S : Type) [Fintype R] [Fintype S] [DecidableEq S]
    (A : Matrix S R (𝓞 K)) (D : Matrix S S (𝓞 K)) (hD : D.det ≠ 0) :
    ∃ H : AddSubgroup (R → 𝓞 K), (∀ x, x ∈ H ↔ ∃ z, A *ᵥ x + D *ᵥ z = 0) ∧ H.index ≠ 0 ∧
      (H.index : ℝ) ≤ ∏ w : InfinitePlace K, w (D.det : 𝓞 K) ^ w.mult := by
  classical
  let gD : (S → 𝓞 K) →ₗ[ℤ] (S → 𝓞 K) := (Matrix.toLin' D).restrictScalars ℤ
  let fA : (R → 𝓞 K) →+ (S → 𝓞 K) := (Matrix.toLin' A).toAddMonoidHom
  let N : AddSubgroup (S → 𝓞 K) := (LinearMap.range gD).toAddSubgroup
  have hinj : Function.Injective gD := LinearMap.ker_eq_bot.mp <| LinearMap.ker_eq_bot'.mpr fun z hz => by
    have h2 : D.det • z = 0 := by
      simpa [gD, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using congrArg D.adjugate.mulVec hz
    exact (smul_eq_zero.mp h2).resolve_left hD
  have hN : N.index = (Algebra.norm ℤ D.det).natAbs :=
    (Submodule.natAbs_det_equiv (LinearMap.range gD) (LinearEquiv.ofInjective gD hinj)).symm.trans <| by
      rw [show (LinearMap.range gD).subtype.comp _ = gD from rfl, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  have hN0 : N.index ≠ 0 := hN ▸ Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hD)
  have hdvd : (N.comap fA).index ∣ N.index :=
    AddSubgroup.index_comap N fA ▸ AddSubgroup.relIndex_dvd_index_of_normal _ _
  refine ⟨N.comap fA, fun x => ?_, fun h0 => hN0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd)),
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd)).trans_eq ?_⟩
  · change (∃ z, D *ᵥ z = A *ᵥ x) ↔ ∃ z, A *ᵥ x + D *ᵥ z = 0
    exact ⟨fun ⟨z, hz⟩ => ⟨-z, by rw [Matrix.mulVec_neg, hz, add_neg_cancel]⟩,
      fun ⟨z, hz⟩ => ⟨-z, by rw [Matrix.mulVec_neg, eq_neg_of_add_eq_zero_right hz, neg_neg]⟩⟩
  · rw [InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int, hN, Nat.cast_natAbs]; push_cast; rfl

theorem exists_rows {K : Type} [Field K] {P S : Type} [Fintype P] [Fintype S] [DecidableEq S] (β : Matrix P S K)
    (h : Function.Injective β.mulVec) : ∃ e : S → P, (β.submatrix e id).det ≠ 0 := by
  have hspan : Submodule.span K (Set.range β.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq <| by
      rw [Matrix.finrank_span_range_row, ← Matrix.finrank_range_mulVecLin,
        LinearMap.finrank_range_of_inj (by simpa [Matrix.coe_mulVecLin] using h)]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K β.row
  have := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  let f : S ≃ κ := Fintype.equivOfCardEq <| by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hsp, hspan, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  exact ⟨a ∘ f, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp (hli.comp f f.injective))).ne_zero⟩

variable {K : Type} [Field K] {N : ℕ}

theorem mul_mul_apply (A x B : Matrix (Fin N) (Fin N) K) (T : Finset (Fin N × Fin N))
    (hx : ∀ i j, (i, j) ∉ T → x i j = 0) (a b : Fin N) :
    (A * x * B) a b = ∑ q ∈ T, A a q.1 * B q.2 b * x q.1 q.2 := by
  rw [Finset.sum_subset (Finset.subset_univ T) fun q _ hq => by simp [hx q.1 q.2 hq],
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem det_upUni {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => (hU i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl

theorem upUni_inv {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : IsUpUni U⁻¹ := by
  have := U.invertibleOfIsUnitDet (Cell.up_det hU)
  have ht := Matrix.blockTriangular_inv_of_blockTriangular (Cell.up_tri hU)
  refine fun i j => ⟨fun h => ht h, ?_⟩; rintro rfl
  have h1 : (U * U⁻¹) i i = 1 := by simp [Matrix.mul_nonsing_inv _ (Cell.up_det hU)]
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => ?_) (by simp), (hU i i).2 rfl, one_mul] at h1
  · exact h1
  · exact hk.lt_or_gt.elim (fun h => by simp [(hU i k).1 h]) (fun h => by simp [ht h])

def conjMat (U : Matrix (Fin N) (Fin N) K) (R : Finset (Fin N × Fin N)) : Matrix R R K :=
  fun q q' => U⁻¹ q.1.1 q'.1.1 * U q'.1.2 q.1.2

theorem det_of_key {n κ : Type} [Fintype n] [DecidableEq n] [LinearOrder κ] (M : Matrix n n K) (k : n → κ)
    (hk : Function.Injective k) (h : ∀ i j, k j < k i → M i j = 0) : M.det = ∏ i, M i i := by
  let _ : LinearOrder n := LinearOrder.lift' k hk
  convert Matrix.det_of_isUpperTriangular (M := M) (fun i j hij => h i j hij)

theorem det_conjMat {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (R : Finset (Fin N × Fin N)) :
    (conjMat U R).det = 1 := by
  have hUi := upUni_inv hU
  rw [det_of_key (conjMat U R) (fun q : R => toLex (q.1.1, OrderDual.toDual q.1.2))]
  · exact Finset.prod_eq_one fun q _ => by simp [conjMat, (hUi _ _).2 rfl, (hU _ _).2 rfl]
  · intro q q' h
    have h' := Prod.ext_iff.1 (toLex.injective h)
    exact Subtype.ext (Prod.ext h'.1 (OrderDual.toDual.injective h'.2))
  · intro q q' h; simp only [conjMat]
    rcases Prod.Lex.lt_iff.1 h with (h1 : q'.1.1 < q.1.1) | ⟨_, h2 : q.1.2 < q'.1.2⟩
    · rw [(hUi _ _).1 h1, zero_mul]
    · rw [(hU _ _).1 h2, mul_zero]

section Cell

variable {Z U : Matrix (Fin N) (Fin N) K} {R : Finset (Fin N × Fin N)}

theorem conjMat_mulVec (hU : IsUpUni U) {x : Matrix (Fin N) (Fin N) K}
    (hx : ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) :
    conjMat U R *ᵥ (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) = fun q : R => x q.1.1 q.1.2 := by
  funext q; conv_rhs => rw [← Cell.conj_cancel (Cell.up_det hU) x]
  rw [mul_mul_apply U⁻¹ (U * x * U⁻¹) U R hx, ← Finset.sum_coe_sort R]; rfl

theorem exists_lie (hU : IsUpUni U) (y : R → K) :
    ∃ x : Matrix (Fin N) (Fin N) K, (∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) ∧ ∀ q : R, x q.1.1 q.1.2 = y q := by
  let w : Matrix (Fin N) (Fin N) K := fun i j => if h : (i, j) ∈ R then ((conjMat U R)⁻¹ *ᵥ y) ⟨(i, j), h⟩ else 0
  have hw : U * (U⁻¹ * w * U) * U⁻¹ = w := by
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Cell.up_det hU),
      Matrix.mul_nonsing_inv_cancel_left _ _ (Cell.up_det hU)]
  have hsupp : ∀ i j, (i, j) ∉ R → (U * (U⁻¹ * w * U) * U⁻¹) i j = 0 := fun i j h => by simp [hw, w, h]
  refine ⟨U⁻¹ * w * U, hsupp, fun q => ?_⟩
  have hd : IsUnit (conjMat U R).det := by rw [det_conjMat hU]; exact isUnit_one
  simp [← congrFun (conjMat_mulVec hU hsupp) q, hw, w, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd]

def coRoots (R : Finset (Fin N × Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ q ∉ R

def eqMat {A : Type} [CommRing A] (Z : Matrix (Fin N) (Fin N) A) (T : Finset (Fin N × Fin N)) :
    Matrix {q : Fin N × Fin N // q.1 ≤ q.2} T A :=
  fun a q => Z a.1.1 q.1.1 * Z.adjugate q.1.2 a.1.2

theorem mem_lieU_iff (hR : ∀ q ∈ R, q.1 < q.2) {x : Matrix (Fin N) (Fin N) K} (hx : StrUp x) :
    x ∈ lieU Z ↔ eqMat Z R *ᵥ (fun q : R => x q.1.1 q.1.2) +
      eqMat Z (coRoots R) *ᵥ (fun q : coRoots R => x q.1.1 q.1.2) = 0 := by
  let _ := hR
  have hsupp : ∀ i j, (i, j) ∉ R ∪ coRoots R → x i j = 0 := fun i j hij =>
    (le_or_gt j i).elim (hx i j) fun hlt => False.elim <| hij <| by simp [coRoots, hlt]; tauto
  have hdisj : Disjoint R (coRoots R) := Finset.disjoint_right.2 fun _ hq => (Finset.mem_filter.1 hq).2.2
  have key (a : {q : Fin N × Fin N // q.1 ≤ q.2}) :
      (eqMat Z R *ᵥ (fun q : R => x q.1.1 q.1.2) +
        eqMat Z (coRoots R) *ᵥ (fun q : coRoots R => x q.1.1 q.1.2)) a =
        (Z * x * Z.adjugate) a.1.1 a.1.2 := by
    rw [mul_mul_apply Z x Z.adjugate _ hsupp, Finset.sum_union hdisj,
      ← Finset.sum_coe_sort R, ← Finset.sum_coe_sort (coRoots R)]; rfl
  exact ⟨fun ⟨_, hlo⟩ => funext fun a => (key a).trans (hlo _ _ a.2),
    fun h => ⟨hx, fun i j hij => (key ⟨(i, j), hij⟩).symm.trans (congrFun h ⟨(i, j), hij⟩)⟩⟩

theorem eqMat_injective (hU : IsUpUni U) (hR : ∀ q ∈ R, q.1 < q.2)
    (hc : ∀ x, x ∈ lieU Z ↔ ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) :
    Function.Injective (eqMat Z (coRoots R)).mulVec := by
  intro v w hvw; rw [← sub_eq_zero]; set u := v - w
  have h0 : eqMat Z (coRoots R) *ᵥ u = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
  let x : Matrix (Fin N) (Fin N) K := fun i j => if h : (i, j) ∈ coRoots R then u ⟨(i, j), h⟩ else 0
  have hxs : StrUp x := fun i j hji => dite_eq_right_iff.2 fun hm => absurd (Finset.mem_filter.1 hm).2.1 hji.not_gt
  have hxR : (fun q : R => x q.1.1 q.1.2) = 0 := funext fun q => dite_eq_right_iff.2 fun hm =>
    absurd q.2 (Finset.mem_filter.1 hm).2.2
  have hxC : (fun q : coRoots R => x q.1.1 q.1.2) = u := funext fun q => dite_eq_left q.2
  have hsupp := (hc x).1 ((mem_lieU_iff hR hxs).2 (by simp [hxR, hxC, h0]))
  have hy : (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_conjMat hU]; exact one_ne_zero) ((conjMat_mulVec hU hsupp).trans hxR)
  have hx0 : x = 0 := by
    rw [← Cell.conj_cancel (Cell.up_det hU) x,
      show U * x * U⁻¹ = 0 from Matrix.ext fun i j => if hij : (i, j) ∈ R then congrFun hy ⟨(i, j), hij⟩ else hsupp i j hij,
      Matrix.mul_zero, Matrix.zero_mul]
  funext q; simpa [hx0] using (congrFun hxC q).symm

end Cell

theorem norm_det_eqMat_le (φ : K →+* ℂ) (Z : Matrix (Fin N) (Fin N) K) (b : ℝ)
    (hb : ∀ (t : ℕ) (I J : Fin t → Fin N), ‖φ ((Z.submatrix I J).det)‖ ≤ b) (T : Finset (Fin N × Fin N))
    (hT : ∀ q ∈ T, q.1 < q.2) (e : T → {q : Fin N × Fin N // q.1 ≤ q.2}) :
    ‖φ ((eqMat Z T).submatrix e id).det‖ ^ 2 ≤ (4 * (N : ℝ) ^ 2 * max 1 b ^ 4) ^ N ^ 2 := by
  have hb1 : 1 ≤ b := by simpa using hb 0 Fin.elim0 Fin.elim0
  rw [max_eq_right hb1]
  have hent (i j : T) : NormedField.toAbsoluteValue ℂ ((φ.mapMatrix ((eqMat Z T).submatrix e id)) i j) ≤ b ^ 2 := by
    show ‖φ (Z _ _ * Z.adjugate _ _)‖ ≤ b ^ 2; rw [map_mul, norm_mul, sq]
    refine mul_le_mul (by simpa [Matrix.det_unique] using hb 1 (fun _ => _) (fun _ => _)) ?_ (norm_nonneg _) (by linarith)
    cases N with
    | zero => exact (e i).1.1.elim0
    | succ n => simpa [Matrix.adjugate_fin_succ_eq_det_submatrix] using hb n _ _
  have hdet : ‖φ ((eqMat Z T).submatrix e id).det‖ ≤ (T.card.factorial : ℝ) * (b ^ 2) ^ T.card := by
    have h := Matrix.det_le hent; rwa [← RingHom.map_det, Fintype.card_coe, nsmul_eq_mul] at h
  have hc : 2 * T.card ≤ N ^ 2 := by
    have hd : Disjoint T (T.image Prod.swap) := Finset.disjoint_left.2 fun q hq hq' => by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq'; exact lt_asymm (hT _ hp) (hT _ hq)
    simpa [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ Prod.swap_injective,
      two_mul, sq] using Finset.card_le_univ (T ∪ T.image Prod.swap)
  have hfac : ((T.card.factorial : ℝ)) ^ 2 ≤ ((N : ℝ) ^ 2) ^ (N ^ 2) := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp [show T.card = 0 by omega]
    · exact_mod_cast (Nat.pow_le_pow_left (T.card.factorial_le_pow.trans
        (Nat.pow_le_pow_left (show T.card ≤ N ^ 2 by omega) _)) 2).trans
        (by rw [← pow_mul, mul_comm _ 2]; exact Nat.pow_le_pow_right (by positivity) hc)
  calc ‖φ ((eqMat Z T).submatrix e id).det‖ ^ 2
        ≤ ((T.card.factorial : ℝ) * (b ^ 2) ^ T.card) ^ 2 := by gcongr
      _ = ((T.card.factorial : ℝ)) ^ 2 * b ^ (4 * T.card) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ (N ^ 2) * b ^ (4 * N ^ 2) :=
          mul_le_mul hfac (pow_le_pow_right₀ hb1 (by omega)) (by positivity) (by positivity)
      _ ≤ 4 ^ (N ^ 2) * (((N : ℝ) ^ 2) ^ (N ^ 2) * b ^ (4 * N ^ 2)) :=
          le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      _ = (4 * (N : ℝ) ^ 2 * b ^ 4) ^ (N ^ 2) := by rw [mul_pow, mul_pow, pow_mul b 4]; ring

theorem domain_of_cell [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) {Z U : Matrix (Fin N) (Fin N) K}
    {R : Finset (Fin N × Fin N)} (B : ℝ) (Bv : ι → ℝ) (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w)
    (hrk : finrank ℚ K = 2 * Fintype.card ι) (hU : IsUpUni U) (hZ : EntIn ⊤ Z)
    (hBv : ∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v ((Z.submatrix I J).det)‖ ≤ Bv v)
    (hprod : ∏ v, max 1 (Bv v) ≤ B) (hR : ∀ q ∈ R, q.1 < q.2)
    (hc : ∀ x, x ∈ lieU Z ↔ ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) (Λ : Submodule ℤ (ι → R → ℂ))
    (hΛ : ∀ c, c ∈ Λ ↔ ∃ x ∈ lieU Z, EntIn ⊤ x ∧ ∀ v (q : R), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) :
    ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ IsAddFundamentalDomain Λ Ω volume ∧ volume Ω ≤
      ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) *
        ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  classical
  have hbij : Function.Bijective (fun v => InfinitePlace.mk (τ v)) :=
    ⟨fun a b h => (hτ _).unique h rfl, fun w => (hτ w).exists⟩
  have hTC : IsTotallyComplex K := nrRealPlaces_eq_zero_iff.mp <| by
    have := Fintype.card_of_bijective hbij
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    omega
  choose Z₀ _ hZo using hZ; let Z' : Matrix (Fin N) (Fin N) (𝓞 K) := Matrix.of Z₀
  have heqMap (T : Finset (Fin N × Fin N)) : (eqMat Z' T).map (algebraMap (𝓞 K) K) = eqMat Z T := by
    have hZmap : Z'.map (algebraMap (𝓞 K) K) = Z := Matrix.ext fun i j => hZo i j
    rw [← hZmap]; ext a q
    have h := congrFun (congrFun (RingHom.map_adjugate (algebraMap (𝓞 K) K) Z') q.1.2) a.1.2
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h; simp [eqMat, h]
  set S := coRoots R; obtain ⟨e, he⟩ := exists_rows _ (eqMat_injective hU hR hc)
  let Ao : Matrix S R (𝓞 K) := (eqMat Z' R).submatrix e id
  let Do : Matrix S S (𝓞 K) := (eqMat Z' S).submatrix e id
  have hDdet : ((Do.det : 𝓞 K) : K) = ((eqMat Z S).submatrix e id).det := by
    show algebraMap (𝓞 K) K Do.det = _; rw [RingHom.map_det, ← heqMap]; rfl
  obtain ⟨H, hH, hHi, hHle⟩ := index_le K R S Ao Do fun h => he (by rw [← hDdet, h]; rfl)
  let M : ι → Matrix R R ℂ := fun v => (conjMat U R).map (τ v)
  have hM (v) : (M v).det = 1 := by
    rw [show M v = (τ v).mapMatrix (conjMat U R) from rfl, ← RingHom.map_det, det_conjMat hU, map_one]
  have hMx (x : Matrix (Fin N) (Fin N) K) (hsx : ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) (v) :
      M v *ᵥ (fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2)) = fun q : R => τ v (x q.1.1 q.1.2) :=
    funext fun q => (conjMat_mulVec hU hsx ▸ RingHom.map_mulVec (τ v) (conjMat U R) _ q).symm
  have hrows (x : Matrix (Fin N) (Fin N) K) (hx : x ∈ lieU Z) :
      (eqMat Z R).submatrix e id *ᵥ (fun q : R => x q.1.1 q.1.2) +
        (eqMat Z S).submatrix e id *ᵥ (fun q : S => x q.1.1 q.1.2) = 0 :=
    funext fun s => congrFun ((mem_lieU_iff hR hx.1).1 hx) (e s)
  have hAD (y : R → 𝓞 K) (z : S → 𝓞 K) : Ao *ᵥ y + Do *ᵥ z = 0 ↔
      (eqMat Z R).submatrix e id *ᵥ (fun q => (y q : K)) +
        (eqMat Z S).submatrix e id *ᵥ (fun q => (z q : K)) = 0 := by
    rw [← Function.Injective.eq_iff (f := fun v : S → 𝓞 K => algebraMap (𝓞 K) K ∘ v)
      (fun a b h => funext fun s => RingOfIntegers.coe_injective (congrFun h s))]
    change (fun s => algebraMap (𝓞 K) K ((Ao *ᵥ y) s + (Do *ᵥ z) s)) = 0 ↔ _
    simp only [map_add, RingHom.map_mulVec, show Ao.map _ = ((eqMat Z' R).map _).submatrix e id from rfl,
      show Do.map _ = ((eqMat Z' S).map _).submatrix e id from rfl, heqMap]; rfl
  have hΛ' (c) : c ∈ Λ ↔ ∃ y ∈ H, ∀ v, M v *ᵥ c v = fun q => τ v (y q) := by
    rw [hΛ c]; constructor
    · rintro ⟨x, hx, hxi, hcx⟩; choose xo _ hxo using hxi
      refine ⟨fun q => xo q.1.1 q.1.2, (hH _).2 ⟨fun s => xo s.1.1 s.1.2, ?_⟩, fun v => ?_⟩
      · exact (hAD _ _).2 (by simpa [hxo] using hrows x hx)
      · rw [funext (hcx v), hMx x ((hc x).1 hx) v]; exact funext fun q => by simp [hxo]
    · rintro ⟨y, hy, hMy⟩
      obtain ⟨z, hz⟩ := (hH y).1 hy; obtain ⟨x, hsx, hxy⟩ := exists_lie hU (fun q : R => (y q : K))
      have hx : x ∈ lieU Z := (hc x).2 hsx
      have hxz : (fun q : S => x q.1.1 q.1.2) = fun q : S => (z q : K) := by
        have k1 := hrows x hx
        rw [show (fun q : R => x q.1.1 q.1.2) = fun q : R => (y q : K) from funext hxy] at k1
        refine sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero he ?_)
        rw [Matrix.mulVec_sub, (add_right_inj _).1 (k1.trans ((hAD y z).1 hz).symm), sub_self]
      refine ⟨x, hx, fun i j => ?_, fun v => ?_⟩
      · by_cases hij : j ≤ i
        · exact ⟨0, Submodule.mem_top, by simp [hx.1 i j hij]⟩
        · by_cases hR' : (i, j) ∈ R
          · exact ⟨y ⟨(i, j), hR'⟩, Submodule.mem_top, (hxy ⟨(i, j), hR'⟩).symm⟩
          · exact ⟨z ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_not_ge hij, hR'⟩⟩,
              Submodule.mem_top, (congrFun hxz _).symm⟩
      · have h2 : M v *ᵥ c v = M v *ᵥ fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2) := by
          rw [hMy v, hMx x hsx v]; exact funext fun q => by simp [hxy]
        exact congrFun <| sub_eq_zero.1 <| Matrix.eq_zero_of_mulVec_eq_zero
          (by rw [hM v]; exact one_ne_zero) (by rw [Matrix.mulVec_sub, h2, sub_self])
  obtain ⟨Ω, hΩm, hΩf, hΩv⟩ := exists_domain K ι τ hτ R H hHi M hM Λ hΛ'
  refine ⟨Ω, hΩm, hΩf, hΩv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hidx : (H.index : ℝ) ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2) :=
    calc (H.index : ℝ) ≤ ∏ w : InfinitePlace K, w ((Do.det : 𝓞 K) : K) ^ w.mult := hHle
      _ = ∏ v, ‖τ v (((eqMat Z S).submatrix e id).det)‖ ^ 2 :=
          (Fintype.prod_bijective _ hbij _ _ fun v => by
            rw [InfinitePlace.mult_isComplex ⟨_, hTC.isComplex _⟩, hDdet, InfinitePlace.apply]).symm
      _ ≤ ∏ v, (4 * (N : ℝ) ^ 2 * max 1 (Bv v) ^ 4) ^ N ^ 2 :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun v _ =>
            norm_det_eqMat_le (τ v) Z (Bv v) (fun t I J => hBv t I J v) S (fun _ hq => (Finset.mem_filter.1 hq).2.1) e
      _ = ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * (∏ v, max 1 (Bv v)) ^ 4) ^ N ^ 2 := by
          rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, Finset.card_univ]
      _ ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ N ^ 2 := by
          have : 0 ≤ ∏ v, max 1 (Bv v) := Finset.prod_nonneg fun _ _ => by positivity
          gcongr
  have ha : (1 : ℝ) ≤ |(discr K : ℝ)| ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast Int.one_le_abs (discr_ne_zero K)) (by norm_num)
  rw [mul_comm]
  exact mul_le_mul (pow_le_pow_right₀ ha (by simpa [Fintype.card_coe, sq] using Finset.card_le_univ R))
    hidx (Nat.cast_nonneg _) (by positivity)

theorem lie_lattice_domain : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N) (B : ℝ) (Bv : ι → ℝ), (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) → finrank ℚ K = 2 * Fintype.card ι → IsLoUni L → IsUpUni U → EntIn ⊤ (L * ptMat p * U) → 1 ≤ B → (∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v (((L * ptMat p * U).submatrix I J).det)‖ ≤ Bv v) → ∏ v, max 1 (Bv v) ≤ B → ∀ Λ : Submodule ℤ (ι → roots (ptMat p) → ℂ), (∀ c, c ∈ Λ ↔ ∃ x ∈ lieU (L * ptMat p * U), EntIn ⊤ x ∧ ∀ v (q : roots (ptMat p)), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) → ∃ Ω : Set (ι → roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.IsAddFundamentalDomain Λ Ω MeasureTheory.volume ∧ MeasureTheory.volume Ω ≤ ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) * ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  intro K _ _ _ ι _ τ N L U p B Bv _ hτ hrk hL hU hZ _ hBv hprod Λ hΛ
  obtain ⟨-, h2, -, h4⟩ := GlobalTheory.LoopV.Cell.stab_cell K N L U p hL hU
  exact domain_of_cell ι τ B Bv hτ hrk hU hZ hBv hprod
    (fun q hq => (Finset.mem_filter.1 hq).2.1) (fun x => (h2 x).trans (h4 _)) Λ hΛ

end GlobalTheory.LieCovol
