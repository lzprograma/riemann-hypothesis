module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbKey
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseRationalsPlusSinglePlaceAdeles
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.CongUnip
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.GramExtendZeroEmbedded
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ProjectedBlockUpperSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HaarLc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SliceFacts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

/-! # SiegelWeilAldSmallSTop: Consolidated global theta-kernel definitions and proofs (SiegelWeilAldSmallSTop). -/
@[expose] public section

noncomputable section
open GlobalTheory.ThK (incV)

section
open scoped TensorProduct NNReal ENNReal Matrix Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
open Matrix (fromBlocks fromBlocks_map fromBlocks_multiply fromBlocks_one single_apply transpose_add transpose_apply
  transpose_mul transpose_one transpose_zero)
open Finset (mul_sum sum_congr sum_eq_zero sum_mul)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace PositivityTheory.SiegelWeilFormula
namespace Ald
theorem smallS_of_k (hC : ChartFacts_k) (hF : SliceFacts) (hU : SubSplit) (hH : HaarLc) : SmallS_k := by
  intro hT F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop hTf
  have hψ := d.ok.good.std
  have hcm := d.ok.good.cm
  have hJ : d.A.J.det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact (_root_.GlobalTheory.isUnit_det_of_isHerm F E σ d.B d.m d.A d.r d.s hA).ne_zero
    · exact (_root_.GlobalTheory.SkewUnit.isUnit_det_of_isSkew F E σ d.B d.m d.A d.r d.s hA).ne_zero
  obtain ⟨hc1, -, -, -, hc5⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  have hlin := d.ok.dbl.lin
  have pres1 : ∀ u : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S u ∘ₗ S1') φ ∈ schA F (K1 d.m n) :=
    fun u φ hφ => hop.pres _ (hlin.pres u _ (hop.pres' φ hφ))
  have one1 : ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S 1 ∘ₗ S1') φ = φ := fun φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_one, one_apply_eq_self]
    exact hop.right φ hφ
  have mul1 : ∀ u v : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n),
      (S1 ∘ₗ d.S (u * v) ∘ₗ S1') φ = (S1 ∘ₗ d.S u ∘ₗ S1') ((S1 ∘ₗ d.S v ∘ₗ S1') φ) := fun u v φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_mul, mul_apply_eq_comp]
    rw [hop.left _ (hlin.pres v _ (hop.pres' φ hφ))]
  obtain ⟨SA1, hSA1⟩ := projHom (fun u => S1 ∘ₗ d.S u ∘ₗ S1') pres1 one1 mul1
  have hsplit : IsUSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm)
      (fun (g : UA σ d.A.J) (x : d.M2) => mat g * x) SA1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop hSA1 hlin
  have hexp : ∀ u : UA σ d.A.J, ∀ Ψ ∈ schA F (K1 d.m n), ∀ x : K1 d.m n → AF F,
      SA1 u Ψ x = Ψ (Sum.elim (Lk d.bs (mat u⁻¹) (x ∘ Sum.inl)) (Lc d.bs (mat u⁻¹) (x ∘ Sum.inr))) := by
    intro u Ψ hΨ x
    set X := cmbB d.bs (x ∘ (eK d.m h).symm) with hX
    have hx : crdB d.bs X ∘ eK d.m h = x := by
      rw [hX, crdB_cmbB]; funext k; simp
    have hΦ : S1' Ψ ∈ d.sch := hop.pres' Ψ hΨ
    have hTP := (hT.2.1 F E σ d (S1' Ψ) hΦ).2.2 u X
    rw [hTf _ (hlin.pres u _ hΦ), hTf _ hΦ, hop.right Ψ hΨ] at hTP
    have key := mul_left_cancel₀ hC0 hTP
    calc SA1 u Ψ x = S1 (d.S u (S1' Ψ)) x := by rw [hSA1 u Ψ hΨ]; rfl
      _ = S1 (d.S u (S1' Ψ)) (crdB d.bs X ∘ eK d.m h) := by rw [hx]
      _ = Ψ (crdB d.bs (mat u⁻¹ * X) ∘ eK d.m h) := key
      _ = _ := by rw [← Lk_crdB, hX, crdB_cmbB, Lk_eK]
  have hbox : ∀ u : UA σ d.A.J, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), ∀ φ'' ∈ schA F (Fin d.m × Fin 2),
      SA1 u (boxFun φ' φ'') = boxFun (φ' ∘ Lk d.bs (mat u⁻¹)) (φ'' ∘ Lc d.bs (mat u⁻¹)) := by
    intro u φ' h' φ'' h''
    funext x
    rw [hexp u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' h' φ'' h'')]
    rfl
  obtain ⟨φ₀, hφ₀, hφ₀1, hφ₀n⟩ := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).2.2.1
  obtain ⟨φa, hφa, hφa1, -⟩ := (hF F (Fin d.m × Fin 2) (Fin d.m × Fin n × Fin 2)).2.2.1
  let c : UA σ d.A.J → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun u => LinearMap.funLeft ℂ ℂ (Lk d.bs (mat u⁻¹))
  have hc : ∀ u φ, c u φ = φ ∘ Lk d.bs (mat u⁻¹) := fun _ _ => rfl
  have presS : ∀ u, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c u φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    intro u φ hφ
    have := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).1 _
      (hsplit.pres u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀))
    rw [hbox u φ hφ φ₀ hφ₀, slice0_box, Function.comp_apply, Lc_zero, hφ₀1, one_smul] at this
    exact this
  have oneS : ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c 1 φ = φ := by
    intro φ _
    have hm : mat (1 : UA σ d.A.J)⁻¹ = 1 := by rw [inv_one]; rfl
    rw [hc, hm]
    funext x
    simp only [Function.comp_apply, Lk_one]
  have mulS : ∀ u v, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c (u * v) φ = c u (c v φ) := by
    intro u v φ _
    rw [hc, hc, hc, mul_inv_rev, show mat (v⁻¹ * u⁻¹) = mat v⁻¹ * mat u⁻¹ from rfl]
    funext x
    simp only [Function.comp_apply, Lk_mul]
  obtain ⟨S', hS'⟩ := projHom c presS oneS mulS
  have hφ₁ : ∀ g : UA σ d.A.J, φ₀ ∘ Lc d.bs (mat g⁻¹) ∈ schA F (Fin d.m × Fin 2) := by
    intro g
    have := sliceL_mem hF (hsplit.pres g _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φa hφa φ₀ hφ₀))
    rw [hbox g φa hφa φ₀ hφ₀] at this
    convert this using 1
    funext x''
    simp only [boxFun, Function.comp_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Lk_zero, hφa1, one_mul]
  have hsplitS :=
    hU F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2) (d.M2)
      (Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)) _ _ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) dd'
          (emb h b d.b) hc1
      (UA σ d.A.J) (UA σ d.A.J) (fun g x => mat g * x) (fun g x => mat g * x) (MonoidHom.id _) continuous_id
      (fun g w' => hc5 g w') SA1 S' hsplit φ₀ hφ₀ hφ₀1 hφ₀n (fun g => ⟨φ₀ ∘ Lc d.bs (mat g⁻¹), hφ₁ g,
        by rw [Function.comp_apply, Lc_zero, hφ₀1],
        fun μ'' hμ'' => hH F E σ hcm d.m d.A.J hJ d.bs g⁻¹ μ'' hμ'' (fun x => ‖φ₀ x‖ₑ ^ 2),
        fun φ' hφ' => by
          show SA1 g (boxFun φ' φ₀) = _
          rw [hbox g φ' hφ' φ₀ hφ₀, hS' g φ' hφ', hc]⟩)
  refine ⟨S', hsplitS, fun g Φ hΦ => ?_⟩
  show S' g Φ 0 = Φ 0
  rw [hS' g Φ hΦ, hc, Function.comp_apply, Lk_zero]
theorem smallS_of'_k : ChartFacts_k → SliceFacts → SmallS_k := fun hC hF => smallS_of_k hC hF (subSplit_of hF) haarLc
end Ald
section
open SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
namespace Afc
section
variable {d : SD_k σ}
section
variable (L : LD_k d)
theorem cong_unip_k (M : d.Mn)
    (h0 : ∀ i, M L.i₀ i = 0 ∧ M i L.i₀ = 0) (u : Fin L.n → AE F E) :
    ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M * (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) = M :=
        by
  have h1 : M * (∑ j, Matrix.single L.i₀ (L.em j) (u j)) = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, single_apply, Matrix.zero_apply]
    refine sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 r).2]
    · simp [hk]
  have h2 : ((∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, single_apply, Matrix.zero_apply, transpose_apply,
      Matrix.map_apply]
    refine sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 s).1]
    · simp [hk]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), transpose_add,
    transpose_one, Matrix.add_mul, Matrix.one_mul, h2, add_zero, Matrix.mul_add, Matrix.mul_one, h1, add_zero]
theorem fc_U_k {nb : d.nA_ → d.G} {lam : Measure d.nA_} {𝓖 : Set
    d.nA_}
    (hc : d.CD nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (T : d.nF_)
    (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (φ : d.G → ℂ) (hφ : ∀ γ' ∈ d.r2, ∀ g, φ (γ' * g) = φ g)
    (u : Fin L.n → AE F E) (hu : u ∈ L.ratV) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hb := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  have hcc : ∀ z, cA σ (cA σ z) = z := kfour.cA_cA' σ hσ
  obtain ⟨v, rfl⟩ := (mem_ratV_iff_k L u).1 hu
  obtain ⟨a', ha'⟩ := hU.1 (GlobalTheory.ThK.incV F v)
  set N0 := ∑ j, Matrix.single L.i₀ (L.em j) (v j) with hN0
  have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  have hN2 : N0 * N0 = 0 := by
    rw [hN0, sum_mul]
    refine sum_eq_zero fun j _ => ?_
    rw [mul_sum]
    refine sum_eq_zero fun j' _ => ?_
    ext r s
    simp only [Matrix.mul_apply, single_apply, Matrix.zero_apply]
    refine sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [hne j]
    · simp [hk]
  let a : GL (Fin d.n) E := ⟨1 + N0, 1 - N0, by
      rw [mul_sub, mul_one, add_mul, one_mul, hN2, add_zero, add_sub_cancel_right], by
      rw [mul_add, mul_one, sub_mul, one_mul, hN2, sub_zero, sub_add_cancel]⟩
  obtain ⟨g, hg, hgf⟩ := levi_ex hσ hb a
  have hA : (1 + ∑ j, Matrix.single L.i₀ (L.em j) (GlobalTheory.ThK.incV F v j)) = incM F (1 + N0) := by
    ext r s
    simp [hN0, incM, Matrix.sum_apply, single_apply, incV, Matrix.one_apply, apply_ite]
  rw [hA] at ha'
  have hgu : uM (incV F v) = g := by
    apply inFrame_injective d.b
    rw [ha', hgf]
    have r1 := (blk_rel hb _ ha').1
    have r2 := (blk_rel hb _ hgf).1
    have r1' := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 r1
    have e1 : a'.map (cA σ) = (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by
      calc a'.map (cA σ) = a'.map (cA σ) * ((incM F (a.1))ᵀ * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ)) := by
            rw [r2, Matrix.mul_one]
        _ = (a'.map (cA σ) * (incM F (a.1))ᵀ) * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by rw [Matrix.mul_assoc]
        _ = _ := by rw [r1', Matrix.one_mul]
    have e2 : a' = incM F (((a⁻¹).1)ᵀ.map σ) := by
      have := congrArg (fun M => M.map (cA σ)) e1
      simpa [Matrix.map_map, Function.comp_def, hcc] using this
    rw [e2]
  have hgm : uM (GlobalTheory.ThK.incV F v) ∈ d.r2 := hgu ▸ hg
  refine fc_levi hσ hb hψ hc _ hgm ha' T T ?_ φ hφ x
  rw [← hA]
  exact cong_unip_k L T.1.1 hs.1 _
theorem fc_deg_k {nb : d.nA_ → d.G} {lam : Measure d.nA_} {𝓖 : Set
    d.nA_}
    (hc : d.CD nb lam 𝓖) (T : d.nF_) (hT : ¬ IsND T) :
    ∃ γ ∈ d.r2, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
      (∀ γ' ∈ d.r2, ∀ g, φ (γ' * g) = φ g) → ∀ x,
        fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x) := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hb := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  obtain ⟨ε, hε⟩ := hb.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have hee := eps_eq_k L hε hε'
  obtain ⟨T0, hT0⟩ := (mem_nF_iff T.1).1 T.2
  have hC := hT0 ▸ (mem_nA_iff hσ hε T.1.1).1 T.1.2
  have hdet : T0.det = 0 := by
    have h1 := not_not.1 hT
    rw [hT0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
    exact kfour.inclR_injective (h1.trans (map_zero _).symm)
  obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨a', ha'⟩ := exists_gl_col v hv0 L.i₀
  obtain ⟨γ, hγ, hγf⟩ := levi_ex hσ hb a'⁻¹
  set M0 := (a'.1.map σ)ᵀ * T0 * a'.1 with hM0
  have hMc : incM F M0 = ((incM F a'.1).map (cA σ))ᵀ * incM F T0 * incM F a'.1 := by
    rw [incM_mapc, incM_tr, hM0, incM_mul', incM_mul']
  have hM0C : incM F M0 ∈ nCond σ d.n ε := hMc ▸ cong_nCond hσ _ _ hC
  have hM0A : incM F M0 ∈ d.nA_ := (mem_nA_iff hσ hε _).2 hM0C
  let T₀ : d.nF_ := ⟨⟨incM F M0, hM0A⟩, (mem_nF_iff _).2 ⟨M0, rfl⟩⟩
  have hsubC : (incM F M0).submatrix L.em L.em ∈ nCond σ L.n ε' := hee ▸ sub_nCond L.em _ hM0C
  let T' : nF σ L.Y L.b := ⟨⟨(incM F M0).submatrix L.em L.em, (mem_nA_iff hσ hε' _).2 hsubC⟩,
    (mem_nF_iff _).2 ⟨M0.submatrix L.em L.em, rfl⟩⟩
  have hcol : ∀ k, M0 k L.i₀ = 0 := fun k => by
    have e1 : M0 k L.i₀ = (((a'.1.map σ)ᵀ * T0) *ᵥ v) k := by
      simp only [hM0, Matrix.mul_apply, Matrix.mulVec, dotProduct, ha']
    rw [e1, ← Matrix.mulVec_mulVec, hTv, Matrix.mulVec_zero, Pi.zero_apply]
  have hrow : ∀ k, M0 L.i₀ k = 0 := fun k => by
    have e0 : ∀ l, ∑ p, σ (v p) * T0 p l = 0 := fun l => by
      have h1 := congrArg σ (congrFun hTv l)

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at h1
      calc ∑ p, σ (v p) * T0 p l = ∑ p, σ (v p) * -(((ε : ℤ) : E) * σ (T0 l p)) :=
            sum_congr rfl fun p _ => by rw [nCond_rat T0 hC l p]
        _ = -(((ε : ℤ) : E) * ∑ p, σ (T0 l p) * σ (v p)) := by
            rw [mul_sum, ← Finset.sum_neg_distrib]
            exact sum_congr rfl fun p _ => by ring
        _ = 0 := by rw [h1, mul_zero, neg_zero]
    simp only [hM0, Matrix.mul_apply, transpose_apply, Matrix.map_apply, ha']
    simp only [e0, zero_mul, Finset.sum_const_zero]
  refine ⟨γ, hγ, T₀, T', ⟨fun i => ⟨?_, ?_⟩, rfl⟩, fun φ _ hφ x => ?_⟩
  · show inclR (AF F) (M0 L.i₀ i) = 0
    rw [hrow, map_zero]
  · show inclR (AF F) (M0 i L.i₀) = 0
    rw [hcol, map_zero]
  refine (fc_levi hσ hb hψ hc γ hγ hγf T₀ T ?_ φ hφ x).symm
  show ((incM F (a'⁻¹).1).map (cA σ))ᵀ * incM F M0 * incM F (a'⁻¹).1 = T.1.1
  rw [hT0, incM_mapc, incM_tr, ← incM_mul', ← incM_mul', hM0]
  congr 1
  have ha : a'.1 * (a'⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((a'⁻¹).1.map σ)ᵀ * ((a'.1.map σ)ᵀ * T0 * a'.1) * (a'⁻¹).1
      = ((a'.1 * (a'⁻¹).1).map σ)ᵀ * T0 * (a'.1 * (a'⁻¹).1) := by
        rw [mapσ_mul', transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = T0 := by rw [ha, Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.one_mul,
        Matrix.mul_one]
end
end
theorem fcConj_of_k : SiegelWeilDatumProperties → FcConj_k := fun _ _F _E _ _ _ _ _ _σ _d L _nb _lam _𝓖 hc =>
  ⟨fun T hT => fc_deg_k L hc T hT, fun _uM _ν _𝓤 hU T T' hs φ _ hφ u hu x => fc_U_k L hc hU T T' hs φ hφ u hu x⟩
end Afc
end
namespace Afc
section
variable (d : SD_k σ)
theorem gram_incM_k (X : d.ME) :
    d.gram (incM F X) (incM F X) = incM F (gE d.A.J σ X) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by ext i j; rfl
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [h1]
  simp only [gE, incM, ← Matrix.transpose_map, ← Matrix.map_mul]
theorem cond_iff_k (X : d.ME) (M : d.Mn) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • M ↔
      ∀ k l, inclR (AF F) (gE d.A.J σ X k l) = (-2 : ℤ) • M k l := by
  rw [gram_incM_k, ← Matrix.ext_iff]
  rfl
theorem orb_zero_k (hmn : d.m < d.n) (T : d.nF_) (hT : IsND T) (Φ : d.Fn) : d.orb T Φ = 0 := by
  have hE : IsEmpty {X : d.ME // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} := by
    refine ⟨fun ⟨X, hX⟩ => ?_⟩
    rw [gram_incM_k] at hX
    have hdet := congrArg Matrix.det hX
    have h0 : (gE d.A.J σ X).det = 0 := by
      by_contra h
      have hu : IsUnit (gE d.A.J σ X) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
      have h1 := Matrix.rank_of_isUnit _ hu
      have h2 : (gE d.A.J σ X).rank ≤ d.m := by
        rw [gE, Matrix.mul_assoc]
        exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
      rw [h1, Fintype.card_fin] at h2
      omega
    have hm : ((gE d.A.J σ X).map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) (gE d.A.J σ X).det :=
      ((inclR (F := F) (AF F)).map_det _).symm
    rw [incM, hm, h0, map_zero, ← Int.cast_smul_eq_zsmul (AE F E), Matrix.det_smul, Fintype.card_fin] at hdet
    exact hT ((isUnit_neg_two_pow d.n).mul_right_eq_zero.1 hdet.symm)
  simp [SD_k.orb, tsum_empty]
end
section Res
variable {d : SD_k σ} (L : LD_k d)
def extendByZeroColumns (X' : Matrix (Fin d.m) (Fin L.n) E) : d.ME := fun a =>
    Function.extend L.em (X' a) 0
theorem extendZeroColumn_apply_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m)
    (j : Fin L.n) : extendByZeroColumns L X' a (L.em j) = X' a j :=
  L.inj.extend_apply _ _ _
theorem not_mem_range_k : L.i₀ ∉ Set.range L.em := fun h => ((L.rng L.i₀).2 h) rfl
theorem extendZeroColumn_apply_missing (X' : Matrix (Fin d.m) (Fin L.n) E)
    (a : Fin d.m) : extendByZeroColumns L X' a L.i₀ = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => not_mem_range_k L ⟨j, hj⟩
theorem cases_idx_k (k : Fin d.n) : k = L.i₀ ∨ ∃ j, L.em j = k := by
  by_cases h : k = L.i₀
  · exact Or.inl h
  · exact Or.inr ((L.rng k).1 h)
theorem hermForm_extendZeroColumn_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (i j : Fin L.n) :
    gE d.A.J σ (extendByZeroColumns L X') (L.em i) (L.em j) = gE d.A.J σ X' i j := by
  simp only [gE_apply, extendZeroColumn_apply_embed]
theorem hermForm_extendZeroColumn_left (X' : Matrix (Fin d.m) (Fin L.n) E) (l : Fin d.n) : gE d.A.J σ
    (extendByZeroColumns L X') L.i₀ l = 0 := by
  simp [gE_apply, extendZeroColumn_apply_missing]
theorem hermForm_extendZeroColumn_right (X' : Matrix (Fin d.m) (Fin L.n) E) (k : Fin d.n) : gE d.A.J σ
    (extendByZeroColumns L X') k L.i₀ = 0 := by
  simp [gE_apply, extendZeroColumn_apply_missing]
theorem gE_sub_k (X : d.ME) (i j : Fin L.n) :
    gE d.A.J σ (X.submatrix id L.em) i j = gE d.A.J σ X (L.em i) (L.em j) := by
  simp only [gE_apply, Matrix.submatrix_apply, id]
theorem col_zero_k (X : d.ME) (h : gE d.A.J σ X L.i₀ L.i₀ = 0) (a : Fin d.m) : X a L.i₀ = 0 :=
    by
  have hA : Aniso σ d.A.J := aniso_of_k d.ok.good (d.ok.sign.elim (fun h => Or.inl h.1) fun h => Or.inr h.1) d.ok.aniso
  have key := hA (fun i => X i L.i₀) (by
    rw [← h, gE_apply]
    simp only [form, Matrix.mulVec, dotProduct, mul_sum, sum_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    ring)
  exact congrFun key a
theorem extension_by_zero_submatrix (X : d.ME) (h : ∀ a, X a L.i₀ = 0) : extendByZeroColumns L
    (X.submatrix id L.em) = X := by
  ext a k
  rcases cases_idx_k L k with rfl | ⟨j, rfl⟩
  · rw [extendZeroColumn_apply_missing, h]
  · rw [extendZeroColumn_apply_embed]; rfl
theorem submatrix_extendZeroColumn (X' : Matrix (Fin d.m) (Fin L.n) E) : (extendByZeroColumns L X').submatrix id L.em =
    X' := by
  ext a j
  exact extendZeroColumn_apply_embed L X' a j
def eqv_k (T : d.nF_) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') :
    {X : d.ME // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Matrix (Fin L.sd.m) (Fin L.sd.n) E // L.sd.gram (incM F X) (incM F X) = (-2 : ℤ) • T'.1.1} where
  toFun X := ⟨X.1.submatrix id L.em, by
    refine (cond_iff_k L.sd _ _).2 fun i j => ?_
    have h := (cond_iff_k d _ _).1 X.2 (L.em i) (L.em j)
    show inclR (AF F) (gE d.A.J σ (X.1.submatrix id L.em) i j) = _
    rw [gE_sub_k, h, hs.2]
    rfl⟩
  invFun X' := ⟨extendByZeroColumns L X'.1, by
    refine (cond_iff_k d _ _).2 fun k l => ?_
    rcases cases_idx_k L k with rfl | ⟨i, rfl⟩
    · rw [hermForm_extendZeroColumn_left, (hs.1 l).1, map_zero, smul_zero]
    rcases cases_idx_k L l with rfl | ⟨j, rfl⟩
    · rw [hermForm_extendZeroColumn_right, (hs.1 _).2, map_zero, smul_zero]
    rw [hermForm_extendZeroColumn_embed]
    have h := (cond_iff_k L.sd _ _).1 X'.2 i j
    refine h.trans ?_
    rw [hs.2]
    rfl⟩
  left_inv X := by
    refine Subtype.ext (extension_by_zero_submatrix L X.1 (col_zero_k L X.1 ?_))
    have h := (cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm)
  right_inv X' := Subtype.ext (submatrix_extendZeroColumn L X'.1)
theorem orb_res_k (T : d.nF_) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (Φ : d.Fn) (Φ' : L.sd.Fn)
    (hr : L.IsRes Φ Φ') : d.orb T Φ = L.sd.orb T' Φ' := by
  unfold SD_k.orb
  refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
  rw [← (eqv_k L T T' hs).tsum_eq]
  refine tsum_congr fun X => ?_
  have hc : ∀ a, X.1 a L.i₀ = 0 := col_zero_k L X.1 (by
    have h := (cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm))
  have hz : ∀ a, (mat g⁻¹ * incM F X.1) a L.i₀ = 0 := fun a => by
    simp [Matrix.mul_apply, incM, hc]
  rw [← hr.2 _ hz]
  congr 1
end Res
theorem orbRes_k : OrbRes_k := fun _F _E _ _ _ _ _ _σ d =>
  ⟨fun hmn T hT Φ => orb_zero_k d hmn T hT Φ, fun L T T' hs Φ Φ' hr => orb_res_k L T T' hs Φ Φ' hr⟩
section Alg
variable {d : SD_k σ} (L : LD_k d)
abbrev uN_k := Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart (σ := σ) (d := d) L
theorem em_ne_k (j : Fin L.n) : L.em j ≠ L.i₀ := Act.ComplexParameterFamilyContinuity.em_ne_k L j
theorem uN_mul_k (u v : Fin L.n → AE F E) : uN_k L u * uN_k L v = 0 :=
  Act.ComplexParameterFamilyContinuity.unipotent_nilpotent_mul_eq_zero L u v
theorem uN_add_k (u v : Fin L.n → AE F E) : uN_k L (u + v) = uN_k L u + uN_k L v := by
  simp only [uN_k, Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Pi.add_apply, Matrix.single_add,
      Finset.sum_add_distrib]
theorem uN_zero_k : uN_k L 0 = 0 := by
  simp [uN_k, Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart]
def uD_k (u : Fin L.n → AE F E) : d.Mn := 1 - ((uN_k L u).map (cA σ))ᵀ
def uZ_k (u : Fin L.n → AE F E) : d.Mn2 :=
  fromBlocks (1 + uN_k L u) 0 0 (uD_k L u)
theorem uZ_mul_k (u v : Fin L.n → AE F E) : uZ_k L u * uZ_k L v = uZ_k L (u + v) := by
  have h1 : (1 + uN_k L u) * (1 + uN_k L v) = 1 + uN_k L (u + v) := by
    rw [uN_add_k, add_mul, mul_add, mul_add, uN_mul_k]
    simp only [one_mul, mul_one, add_zero]
    abel
  have h2 : uD_k L u * uD_k L v = uD_k L (u + v) := by
    simp only [uD_k, uN_add_k, mapc_add, transpose_add]
    have : ((uN_k L u).map (cA σ))ᵀ * ((uN_k L v).map (cA σ))ᵀ = 0 := by
      rw [← transpose_mul, ← mapc_mulU, uN_mul_k, Matrix.map_zero _ (map_zero _), transpose_zero]
    rw [sub_mul, mul_sub, mul_sub, this]
    simp only [one_mul, mul_one, sub_zero]
    abel
  simp only [uZ_k, fromBlocks_multiply, h1, h2, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
theorem uZ_zero_k : uZ_k (σ := σ) L 0 = 1 := by
  simp [uZ_k, uD_k, uN_zero_k, fromBlocks_one]
def Qa_k (ε : ℤˣ) : d.Mn2 :=
  fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0
theorem uZ_unitary_k (ε : ℤˣ) (u : Fin L.n → AE F E) : (uZ_k L u)ᵀ * Qa_k (d := d) ε * (uZ_k L u).map (cA σ) = Qa_k ε :=
    by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hcc := kfour.cA_cA' σ hσ
  have hD : (uD_k (σ := σ) L u).map (cA σ) = 1 - (uN_k L u)ᵀ := by
    ext i j
    simp only [uD_k, Matrix.map_apply, Matrix.sub_apply, transpose_apply, map_sub, hcc, Matrix.one_apply]
    split_ifs <;> simp
  have k1 : (1 + uN_k L u)ᵀ * (1 - (uN_k L u)ᵀ) = 1 := by
    rw [transpose_add, transpose_one, add_mul, one_mul, mul_sub, mul_one,
      ← transpose_mul, uN_mul_k, transpose_zero, sub_zero]
    abel
  have k2 : (uD_k L u)ᵀ * (1 + uN_k L u).map (cA σ) = 1 := by
    rw [uD_k, Matrix.transpose_sub, transpose_one, Matrix.transpose_transpose, mapc_add, mapc_one, sub_mul,
      one_mul, mul_add, mul_one, ← mapc_mulU, uN_mul_k, Matrix.map_zero _ (map_zero _), add_zero]
    abel
  simp only [uZ_k, Qa_k, Matrix.fromBlocks_transpose, fromBlocks_multiply, fromBlocks_map, hD,
    transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, k1]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, k2]
end Alg
section Pts
variable {d : SD_k σ} (L : LD_k d)
theorem conj_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (Z : d.Mn2) (hZ : Zᵀ * Qa_k ε * Z.map (cA σ) = Qa_k ε) :
    (incM F d.b.1 * Z * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1 * Z * incM F (d.b⁻¹).1).map (cA σ) =
      dbl (incM F d.Y.J) := by
  have hF := frame_adelic (F := F) hε
  have hZ' : Zᵀ * fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0 * Z.map (cA σ) =
      fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0 := hZ
  have h1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← transpose_mul, incM_mul_inv, transpose_one]
  have h2 : (incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ) = 1 := by
    rw [← map_cA_mul, incM_mul_inv, mapc_one]
  rw [map_cA_mul, map_cA_mul, transpose_mul,
      transpose_mul]
  calc (incM F (d.b⁻¹).1)ᵀ * (Zᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
        ((incM F d.b.1).map (cA σ) * Z.map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ))
      = (incM F (d.b⁻¹).1)ᵀ * (Zᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
          Z.map (cA σ)) * (incM F (d.b⁻¹).1).map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = (incM F (d.b⁻¹).1)ᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
          (incM F (d.b⁻¹).1).map (cA σ) := by rw [hF, hZ']
    _ = ((incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
          ((incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ)) := by simp only [Matrix.mul_assoc]
    _ = dbl (incM F d.Y.J) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
theorem unitary_of_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (x : d.G) : (inFrame d.b x)ᵀ * Qa_k (d := d) ε * (inFrame d.b x).map (cA σ) = Qa_k ε := by
  have hF := frame_adelic (F := F) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← transpose_mul, incM_inv_mul, transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← map_cA_mul, incM_inv_mul, mapc_one]
  unfold Qa_k
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [map_cA_mul, map_cA_mul, transpose_mul,
      transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]
def uU_k (u : Fin L.n → AE F E) : GL d.N2 (AE F E) where
  val := incM F d.b.1 * uZ_k L u * incM F (d.b⁻¹).1
  inv := incM F d.b.1 * uZ_k L (-u) * incM F (d.b⁻¹).1
  val_inv := (conj_mul_conj d.b _ _).trans (by
    rw [uZ_mul_k, add_neg_cancel, uZ_zero_k, Matrix.mul_one, incM_mul_inv])
  inv_val := (conj_mul_conj d.b _ _).trans (by
    rw [uZ_mul_k, neg_add_cancel, uZ_zero_k, Matrix.mul_one, incM_mul_inv])
theorem uU_mem_k (u : Fin L.n → AE F E) : uU_k L u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  exact conj_mem_k hε _ (uZ_unitary_k L ε u)
def unipotentOfVector (u : Fin L.n → AE F E) : d.G := ⟨uU_k L u, uU_mem_k L u⟩
theorem inFrame_unipotentOfVector (u : Fin L.n → AE F E) : inFrame d.b (unipotentOfVector L u) = uZ_k L u := by
  show incM F (d.b⁻¹).1 * (incM F d.b.1 * uZ_k L u * incM F (d.b⁻¹).1) * incM F d.b.1 = uZ_k L u
  simp only [Matrix.mul_assoc]
  rw [incM_inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      incM_inv_mul, Matrix.one_mul]
theorem unipotentOfVector_add (u v : Fin L.n → AE F E) : unipotentOfVector L (u + v) = unipotentOfVector L u *
    unipotentOfVector L v := by
  refine kfour.inFrame_injective d.b ?_
  rw [inFrame_mul, inFrame_unipotentOfVector, inFrame_unipotentOfVector,
      inFrame_unipotentOfVector, uZ_mul_k]
theorem unipotentOfVector_zero : unipotentOfVector L 0 = 1 := by
  refine kfour.inFrame_injective d.b ?_
  rw [inFrame_one, inFrame_unipotentOfVector, uZ_zero_k]
theorem uN_eq_sum_k (u : Fin L.n → AE F E) : uN_k L u = ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
  simp only [uN_k, Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Matrix.smul_single, smul_eq_mul,
      mul_one]
theorem continuous_uN_k : Continuous (uN_k L) :=
  Act.ComplexParameterFamilyContinuity.continuous_unipotent_nilpotent L
theorem continuous_uZ_k : Continuous (uZ_k (σ := σ) L) := by
  have hD : Continuous (uD_k (σ := σ) L) :=
    continuous_const.sub (((continuous_uN_k L).matrix_map
        (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)).matrix_transpose)
  exact (continuous_const.add (continuous_uN_k L)).matrix_fromBlocks continuous_const continuous_const hD
theorem continuous_unipotentOfVector : Continuous (unipotentOfVector (σ := σ) L) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_const.matrix_mul (continuous_uZ_k L)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul ((continuous_uZ_k L).comp continuous_neg)).matrix_mul continuous_const
theorem blockDiagonal_preserves_form_iff {ε : ℤˣ} (A D : d.Mn)
    (h : (fromBlocks A 0 0 D)ᵀ * Qa_k ε * (fromBlocks A 0 0 D).map (cA σ) = Qa_k ε) :
    Aᵀ * D.map (cA σ) = 1 := by
  have h' := congrArg Matrix.toBlocks₁₂ h
  simpa [Qa_k, Matrix.fromBlocks_transpose, fromBlocks_multiply, fromBlocks_map,
    Matrix.map_zero _ (map_zero _)] using h'
theorem uM_eq_k {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) : uM = unipotentOfVector L := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hcc := kfour.cA_cA' σ hσ
  funext u
  obtain ⟨a', ha'⟩ := h.1 u
  refine kfour.inFrame_injective d.b ?_
  rw [inFrame_unipotentOfVector, ha']
  have e1 := blockDiagonal_preserves_form_iff _ _ (ha' ▸ unitary_of_mem_k hε (uM u))
  have e2 := blockDiagonal_preserves_form_iff _ _ (uZ_unitary_k L ε u)
  have e3 : a'.map (cA σ) = (uD_k L u).map (cA σ) := by
    have e1' : a'.map (cA σ) * (1 + uN_k L u)ᵀ = 1 := mul_eq_one_comm.1 e1
    calc a'.map (cA σ) = a'.map (cA σ) * ((1 + uN_k L u)ᵀ * (uD_k L u).map (cA σ)) := by rw [e2, Matrix.mul_one]
      _ = (uD_k L u).map (cA σ) := by rw [← Matrix.mul_assoc, e1', Matrix.one_mul]
  have e4 : a' = uD_k L u := by
    ext i j
    have := congrArg (cA σ) (congrFun (congrFun e3 i) j)
    simpa [hcc] using this
  rw [e4]
  rfl
end Pts
section Meas
variable {d : SD_k σ} (L : LD_k d)
theorem mem_ratV_k (v : Fin L.n → AE F E) : v ∈ L.ratV ↔ ∃ e, GlobalTheory.ThK.incV F e = v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, funext fun i => by rw [incV_apply]; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, funext fun i => by simp [incV_apply, map_add (f := _)]⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, funext fun i => by simp [incV_apply, map_neg]⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩
theorem ratV_discrete_k : DiscreteTopology L.ratV :=
  Act.ComplexParameterFamilyContinuity.ratVec_discrete (F := F) (E := E) L.n
theorem ratV_cocompact_k : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ x, ∃ γ ∈ L.ratV, γ + x ∈ K :=
  Act.ComplexParameterFamilyContinuity.ratVec_cocompact (F := F) (E := E) L.n
theorem exists_udata_k : ∃ uM ν 𝓤, L.UData uM ν 𝓤 := by
  have := ratV_discrete_k L
  obtain ⟨K, hK, hc⟩ := ratV_cocompact_k L
  obtain ⟨ν, 𝓤, hν, h𝓤, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (Fin L.n → AE F E) L.ratV K hK hc).1
  exact ⟨unipotentOfVector L, ν, 𝓤, fun u => ⟨uD_k L u, inFrame_unipotentOfVector L u⟩, hν, h𝓤, h1⟩
end Meas
section Dens
variable (d : SD_k σ)
def Sw_k (w : InfinitePlace F) : Set (AE F E) := {z | (∀ w', w' ≠ w → piInf (d.B.emb w') z = 0) ∧ finOne F • z = 0}
theorem sum_mem_Sw_k (w : InfinitePlace F) (s : Fin (Module.finrank F E) → AF F) (hs : ∀ k, (s k).2 = 0 ∧ ∀ w', w' ≠ w →
    (s k).1 w' = 0) :
    ∑ k, s k • kfour.bsA F E k ∈ Sw_k d w := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · rw [map_sum]
    refine sum_eq_zero fun k _ => ?_
    rw [St.piInf_smul, (hs k).2 w' hw', map_zero, zero_mul]
  · rw [Finset.smul_sum]
    refine sum_eq_zero fun k _ => ?_
    rw [smul_smul, finOne_mul (hs k).1, zero_smul]
theorem dense_Sw_k (w : InfinitePlace F) : Dense {z : AE F E | ∃ e : E, ∃ s ∈ Sw_k d w, inclR (F := F) (AF F) e + s =
    z} := by
  have hA := _root_.GlobalTheory.CompanionTheory.AddSA.dense_add_place F w
  let Φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun a => ∑ k, a k • kfour.bsA F E k
  have hΦc : Continuous Φ := continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have hΦs : Function.Surjective Φ := fun z => ⟨fun k => (kfour.bsA F E).repr z k, (kfour.bsA F E).sum_repr z⟩
  have hd : Dense (Set.univ.pi fun _ : Fin (Module.finrank F E) =>
      (Set.range (algebraMap F (AF F)) + {a : AF F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0})) :=
    dense_pi _ fun k _ => hA
  refine (hΦs.denseRange.dense_image hΦc hd).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  choose x hx s hs hxs using fun k => Set.mem_add.1 (ha k (Set.mem_univ k))
  choose q hq using hx
  refine ⟨∑ k, q k • kfour.bsE F E k, ∑ k, s k • kfour.bsA F E k, sum_mem_Sw_k d w s hs, ?_⟩
  have h1 : inclR (AF F) (∑ k, q k • kfour.bsE F E k) = ∑ k, algebraMap F (AF F) (q k) • kfour.bsA F E k := by

    rw [map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_apply, algebraMap_smul, kfour.inclR_eq, TensorProduct.tmul_smul]
  rw [h1, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← add_smul, hq, hxs]
theorem dense_vec_k (k : ℕ) (w : InfinitePlace F) :
    Dense {v : Fin k → AE F E | ∃ e : Fin k → E, ∃ s : Fin k → AE F E, (∀ j, s j ∈ Sw_k d w) ∧
            incV F e + s = v} := by
  refine (dense_pi Set.univ fun j _ => dense_Sw_k d w).mono ?_
  intro v hv
  choose e s hs hes using fun j => hv j (Set.mem_univ j)
  exact ⟨e, s, hs, funext fun j => hes j⟩
end Dens
section Real
variable {d : SD_k σ} (L : LD_k d)
theorem cw_uN_k (w' : InfinitePlace F) (u : Fin L.n → AE F E) :
    d.cw w' (uN_k L u) = ∑ j, Matrix.single L.i₀ (L.em j) (piInf (d.B.emb w') (u j)) := by
  ext a b

  simp only [SD_k.cw, uN_k, Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Matrix.map_apply,
      Matrix.sum_apply, map_sum, single_apply]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp
theorem fin_uN_k (u : Fin L.n → AE F E) : finOne F • uN_k L u = ∑ j, Matrix.single L.i₀ (L.em j) (finOne F • u j) := by
  simp only [uN_k, Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Finset.smul_sum, Matrix.smul_single]
theorem cw_uZ_k (w' : InfinitePlace F) (u : Fin L.n → AE F E) :
    d.cw w' (uZ_k L u) = fromBlocks (1 + d.cw w' (uN_k L u)) 0 0 (1 - ((d.cw w' (uN_k L u)).map star)ᵀ) := by
  have e1 : d.cw w' (1 + uN_k L u) = 1 + d.cw w' (uN_k L u) := by
    rw [SD_k.cw, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have e2 : d.cw w' (uD_k L u) = 1 - ((d.cw w' (uN_k L u)).map star)ᵀ := by
    rw [SD_k.cw, uD_k, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.transpose_map,
      Place.map_cA d.cm]
    rfl
  rw [uZ_k, ← e1, ← e2]
  simp only [SD_k.cw, fromBlocks_map, Matrix.map_zero _ (map_zero _)]
theorem fin_uZ_k (u : Fin L.n → AE F E) :
    finOne F • uZ_k L u = fromBlocks (finOne F • 1 + finOne F • uN_k L u) 0 0
      (finOne F • 1 - ((finOne F • uN_k L u).map (cA σ))ᵀ) := by
  rw [uZ_k, uD_k, Matrix.fromBlocks_smul, smul_zero, smul_add, smul_sub, Krd.map_cA_smul, Matrix.transpose_smul]
end Real
theorem exists_iota_k {d : SD_k σ} (R : RD_k d) (L : LD_k d) (w : InfinitePlace F) (u : Fin L.n → AE F E) (hu : ∀ j,
    u j ∈ Sw_k d w) :
    ∃ y, unipotentOfVector L u = R.ι w y := by
  have h0 := Krd.zeta_ne R.hζ
  set Z := d.cw w (uZ_k L u) with hZdef
  set Z' := d.cw w (uZ_k L (-u)) with hZ'def
  have hZZ : Z * Z' = 1 := by rw [hZdef, hZ'def, ← Krd.cw_mul_k, uZ_mul_k, add_neg_cancel, uZ_zero_k, Krd.cw_one_k]
  have hZZ' : Z' * Z = 1 := by rw [hZdef, hZ'def, ← Krd.cw_mul_k, uZ_mul_k, neg_add_cancel, uZ_zero_k, Krd.cw_one_k]
  have hq : d.cw w (Qa_k R.ε) = Krd.Qc d.n R.ε := by
    ext (i | i) (j | j) <;> simp [Qa_k, Krd.Qc, SD_k.cw, Matrix.one_apply]; split_ifs <;> simp
  have hQ : Zᵀ * Krd.Qc d.n R.ε * Z.map star = Krd.Qc d.n R.ε := by
    have h := congrArg (d.cw w) (uZ_unitary_k L R.ε u)
    rw [Krd.cw_mul_k, Krd.cw_mul_k, Krd.cw_transpose_k, Place.cw_cA_k, hq] at h
    exact h
  let y : GR d.n := ⟨⟨dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹, dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹, by
      rw [show dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹) =
        dZ d.n R.ζ * Z * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * Z' * dZ d.n R.ζ⁻¹ by simp only [Matrix.mul_assoc],
        Krd.dZ_inv_mul h0, Matrix.mul_one, Matrix.mul_assoc (dZ d.n R.ζ), hZZ, Matrix.mul_one, Krd.dZ_mul_inv h0], by
      rw [show dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹) =
        dZ d.n R.ζ * Z' * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * Z * dZ d.n R.ζ⁻¹ by simp only [Matrix.mul_assoc],
        Krd.dZ_inv_mul h0, Matrix.mul_one, Matrix.mul_assoc (dZ d.n R.ζ), hZZ', Matrix.mul_one, Krd.dZ_mul_inv h0]⟩,
    Krd.inG_conj R.hζ Z hQ⟩
  refine ⟨y, kfour.inFrame_injective d.b ?_⟩
  rw [inFrame_unipotentOfVector]
  refine Place.cw_ext_k d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      have h1 := R.at_w w' y
      have h2 : dZ d.n R.ζ * d.cw w' (inFrame d.b (R.ι w' y)) = dZ d.n R.ζ * Z := by
        rw [h1]
        show dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ = dZ d.n R.ζ * Z
        rw [Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]
      have h3 := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) h2
      simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at h3
      exact h3.symm
    · have hN : d.cw w' (uN_k L u) = 0 := by
        rw [cw_uN_k]
        exact sum_eq_zero fun j _ => by rw [(hu j).1 w' hw', Matrix.single_zero]
      rw [R.off_w w w' y hw', cw_uZ_k, hN]
      simp [fromBlocks_one]
  · have hN : finOne F • uN_k L u = 0 := by
      rw [fin_uN_k]
      exact sum_eq_zero fun j _ => by rw [(hu j).2, Matrix.single_zero]
    rw [R.off_f w y, fin_uZ_k, hN]
    simp only [Matrix.map_zero _ (map_zero _), transpose_zero, sub_zero, add_zero]
    conv_rhs => rw [← fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
theorem uEx_k : UEx_k := by
  intro F E _ _ _ _ _ σ d R L
  refine ⟨exists_udata_k L, ?_⟩
  intro uM ν 𝓤 hU w φ hφ hrat hw u x
  have he := uM_eq_k L hU
  subst he
  have := (kfour.doubled_group_topological_properties σ d.Y).1
  let S : AddSubgroup (Fin L.n → AE F E) :=
    { carrier := {u | ∀ x, φ (unipotentOfVector L u * x) = φ x}
      add_mem' := fun {a b} ha hb x => by
        show φ (unipotentOfVector L (a + b) * x) = φ x
        rw [unipotentOfVector_add, mul_assoc, ha, hb]
      zero_mem' := fun x => by
        show φ (unipotentOfVector L 0 * x) = φ x
        rw [unipotentOfVector_zero, one_mul]
      neg_mem' := fun {a} ha x => by
        show φ (unipotentOfVector L (-a) * x) = φ x
        have := ha (unipotentOfVector L (-a) * x)
        rw [← mul_assoc, ← unipotentOfVector_add, add_neg_cancel, unipotentOfVector_zero, one_mul] at this
        exact this.symm }
  have hS : IsClosed (S : Set (Fin L.n → AE F E)) := by
    have : (S : Set (Fin L.n → AE F E)) = ⋂ x, {u | φ (unipotentOfVector L u * x) = φ x} := by
      ext u
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      rfl
    rw [this]
    exact isClosed_iInter fun x => isClosed_eq (hφ.comp
        ((continuous_unipotentOfVector L).mul continuous_const)) continuous_const
  have hT : {v : Fin L.n → AE F E | ∃ e : Fin L.n → E, ∃ s : Fin L.n → AE F E, (∀ j, s j ∈ Sw_k d w) ∧
      GlobalTheory.ThK.incV F e + s = v} ⊆ S := by
    rintro _ ⟨e, s, hs, rfl⟩
    refine S.add_mem (fun x => hrat _ ((mem_ratV_k L _).2 ⟨e, rfl⟩) x) ?_
    obtain ⟨y, hy⟩ := exists_iota_k R L w s hs
    exact fun x => hw s y hy x
  have hu : u ∈ S := by
    have h1 := closure_minimal hT hS
    rw [(dense_vec_k d L.n w).closure_eq] at h1
    exact h1 (Set.mem_univ u)
  exact hu x
end Afc
end PositivityTheory.SiegelWeilFormula
end
end
