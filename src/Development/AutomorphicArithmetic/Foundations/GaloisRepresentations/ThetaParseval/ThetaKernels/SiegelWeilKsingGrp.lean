module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ArchimedeanJacquetFirstTerm.ArchimedeanWhittakerTrace.LZfcCore
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.FrameOfSig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocJJA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.MatrixRepMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.WeylCubeConjUnipotent
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.BddOfPer
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.ContinuousMkG
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
public import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TsContinuousNU
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CharacterQuadraticDerivativeZero

/-! # SiegelWeilKsingGrp: Consolidated global theta-kernel definitions and proofs (SiegelWeilKsingGrp). -/
@[expose] public section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open UpperTheory.TP.W (GoodK)
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open Matrix (fromBlocks fromBlocks_multiply fromBlocks_map fromBlocks_transpose fromBlocks_smul fromBlocks_one
  fromBlocks_inj transpose_map transpose_mul transpose_one conjTranspose_smul conjTranspose_mul conjTranspose_apply
  trace_add trace_zero trace_smul det_smul det_one toBlocks₁₁ toBlocks₁₂ toBlocks₂₁ toBlocks₂₂)
open Finset (sum_congr sum_add_distrib mul_sum)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
private abbrev RM (d : SD_k σ) := Fin d.n → Fin d.n → ℝ
theorem SD_k.cm (d : SD_k σ) : IsCMExt F E σ := d.ok.good.cm
theorem SD_k.std (d : SD_k σ) : IsStd d.B.ψ := d.ok.good.std
namespace Place
variable (d : SD_k σ)
theorem continuous_cw_k (w : InfinitePlace F) {p q : Type} : Continuous (fun X : Matrix p q (AE F E) => d.cw w X) :=
  continuous_id.matrix_map (continuous_piInf (d.B.emb w))
theorem cw_ext_k {p q : Type} {X Z : Matrix p q (AE F E)} (h1 : ∀ w, d.cw w X = d.cw w Z)
    (h2 : finOne F • X = finOne F • Z) : X = Z := mat_ext d.cm d.B.emb h1 h2
theorem cw_cA_k (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) :
    d.cw w (X.map (cA σ)) = (d.cw w X).map star := map_cA d.cm _ X
end Place
namespace Krd
variable (d : SD_k σ)
def sc_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sc_cont_k : Continuous (sc_k d) := (Place.exists_sec d.cm d.B.emb).choose_spec.1
theorem sc_pi_k (x : InfinitePlace F → ℂ) (w : InfinitePlace F) : piInf (d.B.emb w) (sc_k d x) = x w :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.1 x w
theorem sc_fin_k (x : InfinitePlace F → ℂ) : finOne F • sc_k d x = 0 :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.1 x
theorem sc_add_k (x y : InfinitePlace F → ℂ) : sc_k d (x + y) = sc_k d x + sc_k d y :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.2.1 x y
section Glue
variable {p : Type} [DecidableEq p]
def atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : Matrix p p (AE F E) :=
  Matrix.of fun i j => sc_k d (fun w' => fam w Z w' i j) + finOne F • (1 : Matrix p p (AE F E)) i j
theorem cw_mul_k {p q r : Type} [Fintype q] (w : InfinitePlace F) (A : Matrix p q (AE F E))
    (B : Matrix q r (AE F E)) : d.cw w (A * B) = d.cw w A * d.cw w B := Matrix.map_mul (f := piInf (d.B.emb w))
theorem cw_one_k {q : Type} [DecidableEq q] (w : InfinitePlace F) : d.cw w (1 : Matrix q q (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_atM_k (w w' : InfinitePlace F) (Z : Matrix p p ℂ) : d.cw w' (atM_k d w Z) = fam w Z w' := by
  ext i j; simp only [SD_k.cw, Matrix.map_apply, atM_k, Matrix.of_apply, map_add (f := _), sc_pi_k,
    Place.piInf_finOne, add_zero]
theorem fin_atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) :
    finOne F • atM_k d w Z = finOne F • (1 : Matrix p p (AE F E)) := by
  ext i j; simp only [Matrix.smul_apply, atM_k, Matrix.of_apply, smul_add, sc_fin_k, zero_add, smul_smul, fin_idem]
theorem atM_mul_k [Fintype p] (w : InfinitePlace F) (Z Z' : Matrix p p ℂ) :
    atM_k d w (Z * Z') = atM_k d w Z * atM_k d w Z' := by
  refine Place.cw_ext_k d (fun w' => ?_) (by rw [fin_mul, fin_atM_k, fin_atM_k, fin_atM_k, ← fin_mul, mul_one])
  rw [cw_mul_k, cw_atM_k, cw_atM_k, cw_atM_k]; unfold fam; split_ifs <;> simp
theorem atM_one_k (w : InfinitePlace F) : atM_k d w (1 : Matrix p p ℂ) = 1 :=
  Place.cw_ext_k d (fun w' => by rw [cw_atM_k, cw_one_k]; unfold fam; split_ifs <;> rfl) (fin_atM_k d w 1)
private theorem continuous_atM_k (w : InfinitePlace F) : Continuous (atM_k (p := p) d w) :=
  continuous_pi fun i => continuous_pi fun j => ((sc_cont_k d).comp (continuous_pi fun w' => by
    unfold fam; split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
    · exact continuous_const)).add continuous_const
end Glue
theorem bb_k : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by rw [← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul', Units.mul_inv, incM_one]
theorem bb'_k : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by rw [← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul', Units.inv_mul, incM_one]
theorem dbl_incM_k : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  simp only [dbl, incM, fromBlocks_map, Matrix.map_zero _ (map_zero _)]; congr 1; ext i j; simp
theorem cw_transpose_k {p q : Type} (w : InfinitePlace F) (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ :=
  transpose_map
theorem cw_incM_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) :
    d.cw w (incM F M) = M.map (d.B.emb w).1 :=
  Matrix.ext fun i j => PositivityTheory.ThKG.Tow.Levi.piInf_incl (d.B.emb w) (M i j)
private theorem map_sig_emb_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) :
    (M.map σ).map (d.B.emb w).1 = (M.map (d.B.emb w).1).map star := Matrix.ext fun _ _ => d.cm.2.2.2 _ _
theorem hQ_w_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 * (d.b.1.map (d.B.emb w).1).map star = Qc d.n ε := by
  have h := congrArg (fun M => M.map (d.B.emb w).1) hε
  simp only [Matrix.map_mul (f := (d.B.emb w).1), map_sig_emb_k] at h; rw [transpose_map] at h; rw [h]
  simp only [Qc, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1; ext i j; by_cases hij : i = j <;> simp [hij]
private def Zm_k (ζ : ℂ) (y : GR d.n) : M2 d.n := dZ d.n ζ⁻¹ * mR y * dZ d.n ζ
private def MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : d.Mn2 :=
  incM F d.b.1 * atM_k d w (Zm_k d ζ y) * incM F (d.b⁻¹).1
private theorem MxI_mul_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) (y y' : GR d.n) :
    MxI_k d w ζ (y * y') = MxI_k d w ζ y * MxI_k d w ζ y' := by
  have hZm : Zm_k d ζ (y * y') = Zm_k d ζ y * Zm_k d ζ y' := by
    simp only [Zm_k, show mR (y * y') = mR y * mR y' from rfl, mul_assoc]
    rw [← mul_assoc (dZ d.n ζ) (dZ d.n ζ⁻¹), dZ_mul_inv h, one_mul]
  simp only [MxI_k, hZm, atM_mul_k, mul_assoc]; rw [← mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), bb'_k, one_mul]
private theorem MxI_one_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) : MxI_k d w ζ 1 = 1 := by
  have hZ1 : Zm_k d ζ 1 = 1 := by simp only [Zm_k, show mR (1 : GR d.n) = 1 from rfl, mul_one, dZ_inv_mul h]
  rw [MxI_k, hZ1, atM_one_k, mul_one, bb_k]
private theorem inFrame_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) :
    incM F (d.b⁻¹).1 * MxI_k d w ζ y * incM F d.b.1 = atM_k d w (Zm_k d ζ y) := by
  simp only [MxI_k, mul_assoc]; rw [bb'_k, mul_one, ← mul_assoc, bb'_k, one_mul]
private theorem fin_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : finOne F • MxI_k d w ζ y = finOne F • 1 := by
  rw [MxI_k, fin_mul, fin_mul, fin_atM_k, ← fin_mul, ← fin_mul, mul_one, bb_k]
private theorem MxI_unitary_k {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    (MxI_k d w ζ y)ᵀ * dbl (incM F d.Y.J) * (MxI_k d w ζ y).map (cA σ) = dbl (incM F d.Y.J) := by
  refine Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [cw_mul_k, cw_mul_k, Place.cw_cA_k, cw_transpose_k, dbl_incM_k, cw_incM_k,
      show d.cw w' (MxI_k d w ζ y) = d.b.1.map (d.B.emb w').1 * fam w (Zm_k d ζ y) w' * (d.b⁻¹).1.map (d.B.emb w').1
        by rw [MxI_k, cw_mul_k, cw_mul_k, cw_incM_k, cw_incM_k, cw_atM_k]]
    refine conj_unit _ _ _ _ _ (by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (hQ_w_k d hε w') ?_
    unfold fam; split_ifs; · exact (unitary_iff hζ (mR y)).2 y.2
    · rw [transpose_one, mapStar_one, one_mul, mul_one]
  · have e1 : (finOne F • (1 : d.Mn2)).map (cA σ) = finOne F • 1 := by
      rw [map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [fin_mul, fin_mul, ← Matrix.transpose_smul, fin_MxI_k, ← map_cA_smul, fin_MxI_k, e1, Matrix.transpose_smul,
      transpose_one, ← fin_mul, ← fin_mul, mul_one, one_mul]
private def iota_k {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : GR d.n →* d.G where
  toFun y := ⟨⟨MxI_k d w ζ y, MxI_k d w ζ y⁻¹,
    by rw [← MxI_mul_k d (zeta_ne hζ), mul_inv_cancel, MxI_one_k d (zeta_ne hζ)],
    by rw [← MxI_mul_k d (zeta_ne hζ), inv_mul_cancel, MxI_one_k d (zeta_ne hζ)]⟩, MxI_unitary_k d hε hζ w y⟩
  map_one' := Subtype.ext (Units.ext (MxI_one_k d (zeta_ne hζ) w))
  map_mul' a b := Subtype.ext (Units.ext (MxI_mul_k d (zeta_ne hζ) w a b))
private theorem mk_iota {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    ∃ ι : InfinitePlace F → (GR d.n →* d.G), (∀ w, Continuous (ι w)) ∧
      (∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ) ∧
      (∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1) ∧
      ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : d.Mn2) := by
  refine ⟨iota_k d hε hζ, fun w => ?_, fun w y => ?_, fun w w' y hw => ?_, fun w y => ?_⟩
  · have hM : Continuous fun y : GR d.n => MxI_k d w ζ y :=
      (continuous_const.matrix_mul ((continuous_atM_k d w).comp
        ((continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtypeVal)).matrix_mul
          continuous_const))).matrix_mul continuous_const
    exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hM, hM.comp continuous_inv⟩)
  · rw [show inFrame d.b (iota_k d hε hζ w y) = atM_k d w (Zm_k d ζ y) from inFrame_MxI_k d w ζ y, cw_atM_k]
    simp only [fam, ite_true, Zm_k]; rw [← mul_assoc, ← mul_assoc, dZ_mul_inv (zeta_ne hζ), one_mul]
  · rw [show inFrame d.b (iota_k d hε hζ w y) = atM_k d w (Zm_k d ζ y) from inFrame_MxI_k d w ζ y, cw_atM_k]
    simp only [fam, ite_eq_right hw]
  · rw [show inFrame d.b (iota_k d hε hζ w y) = atM_k d w (Zm_k d ζ y) from inFrame_MxI_k d w ζ y, fin_atM_k]
theorem rdEx_k : RDEx_k := fun F E _ _ _ _ _ σ d => by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have key (c : E) (hc : ∀ i j, σ (d.Y.J j i) = c * d.Y.J i j) : ((ε : ℤ) : E) = c := by
    have e := congrFun₂ (conjT_frame c d.Y.J hc (PositivityTheory.ThKG.Tow.Levi.sig_sig d.cm) d.b.1)
      (Sum.inl ⟨0, d.ok.hn⟩) (Sum.inr ⟨0, d.ok.hn⟩)
    rw [hε] at e; simpa [fromBlocks] using e
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he : ε = -1 := Units.ext (Int.cast_injective (α := E) (by
      rw [key (-1) fun i j => by rw [hY, neg_one_mul]]; simp))
    subst he; choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    obtain ⟨ι, hc, ha, ho, hf⟩ := mk_iota d hε (Or.inl ⟨rfl, rfl⟩)
    exact ⟨⟨-1, 1, fr, sg, ι, hε, Or.inl ⟨rfl, rfl⟩, fun w => by rw [one_smul, hfr w], hc, ha, ho, hf⟩⟩
  · have he : ε = 1 := Units.ext (Int.cast_injective (α := E) (by
      rw [key 1 fun i j => by rw [hY, one_mul]]; simp))
    subst he; choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    obtain ⟨ι, hc, ha, ho, hf⟩ := mk_iota d hε (Or.inr ⟨rfl, rfl⟩)
    exact ⟨⟨1, Complex.I, fr, sg, ι, hε, Or.inr ⟨rfl, rfl⟩,
      fun w => by rw [← hfr w, Matrix.mul_smul, Matrix.smul_mul], hc, ha, ho, hf⟩⟩
end Krd
namespace KW
theorem cw_loc_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (X : d.MxE) :
    d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  rw [show (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X from Matrix.ext fun _ _ => star_star _,
    ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
theorem cw_gram_k (d : SD_k σ) (w : InfinitePlace F) (X Z : d.MxE) :
    d.cw w (d.gram X Z) = (d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * (d.cw w Z).map star := by
  unfold SD_k.gram
  rw [Krd.cw_mul_k, Krd.cw_mul_k, Krd.cw_transpose_k, Krd.cw_incM_k, Place.cw_cA_k]
theorem zeta_ne_k {d : SD_k σ} (R : RD_k d) : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
theorem frJ_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) :
    (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
  calc _ = R.ζ⁻¹ • (R.ζ • ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star)) := by
        rw [smul_smul, inv_mul_cancel₀ (zeta_ne_k R), one_smul]
    _ = _ := by rw [R.hfr w, smul_smul]
end KW
namespace KFock
theorem crd_cmb_k (d : SD_k σ) (c : d.I3 → AF F) : d.crd (d.cmb c) = c := funext fun ⟨i, j, l⟩ => by
  have e : d.cmb c i j = ∑ k, c (i, j, k) • (Algebra.TensorProduct.basis (AF F) d.bs) k := by
    simp only [SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  show (Algebra.TensorProduct.basis (AF F) d.bs).repr (d.cmb c i j) l = c (i, j, l)
  rw [e, Module.Basis.repr_sum_self]
private theorem detIm_ne_k (d : SD_k σ) (w : InfinitePlace F) :
    ((d.B.emb w).1 (d.bs 0)).im * ((d.B.emb w).1 (d.bs 1)).re -
      ((d.B.emb w).1 (d.bs 0)).re * ((d.B.emb w).1 (d.bs 1)).im ≠ 0 := by
  have := d.cm.1; have := d.cm.2.1; set τ : E →+* ℂ := (d.B.emb w).1
  have hreal (f : F) : (τ (algebraMap F E f)).im = 0 := by
    have e4 := RingHom.congr_fun
      (ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (IsTotallyReal.isReal w))) f
    rw [ComplexEmbedding.conjugate_coe_eq] at e4
    rw [show τ (algebraMap F E f) = w.embedding f from RingHom.congr_fun (d.B.emb w).2 f]
    exact Complex.conj_eq_iff_im.mp e4
  have hexp (e : E) : τ e = τ (algebraMap F E (d.bs.repr e 0)) * τ (d.bs 0) +
      τ (algebraMap F E (d.bs.repr e 1)) * τ (d.bs 1) := by
    conv_lhs => rw [← d.bs.sum_repr e]
    simp [Fin.sum_univ_two, Algebra.smul_def, map_add (f := _), map_mul]
  obtain ⟨e, he⟩ : ∃ e : E, (τ e).im ≠ 0 := by
    by_contra hne; push Not at hne
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    rw [InfinitePlace.isComplex_mk_iff] at hc
    exact hc (ComplexEmbedding.isReal_iff.mpr <| RingHom.ext fun x => by
      rw [ComplexEmbedding.conjugate_coe_eq]; exact Complex.conj_eq_iff_im.mpr (hne x))
  intro hD; apply he; have h1 := hexp 1; have h2 := hexp e
  set p := τ (algebraMap F E (d.bs.repr 1 0)); set q := τ (algebraMap F E (d.bs.repr 1 1))
  set p' := τ (algebraMap F E (d.bs.repr e 0)); set q' := τ (algebraMap F E (d.bs.repr e 1))
  have ip : p.im = 0 := hreal _; have iq : q.im = 0 := hreal _
  have ip' : p'.im = 0 := hreal _; have iq' : q'.im = 0 := hreal _
  rw [map_one] at h1
  have h1re := congrArg Complex.re h1; have h1im := congrArg Complex.im h1; have h2im := congrArg Complex.im h2
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    ip, iq, ip', iq', zero_mul, sub_zero, add_zero] at h1re h1im h2im
  linear_combination -(p'.re * (τ (d.bs 0)).re + q'.re * (τ (d.bs 1)).re) * h1im -
    (p.re * q'.re - q.re * p'.re) * hD + (p'.re * (τ (d.bs 0)).im + q'.re * (τ (d.bs 1)).im) * h1re + h2im
theorem archEquiv_k (d : SD_k σ) (R : RD_k d) :
    ∃ L : (d.I3 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ),
      ∀ (c : d.I3 → AF F) (w : InfinitePlace F),
        L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c) := by
  have := d.cm.1; have hr : ∀ w : InfinitePlace F, w.IsReal := IsTotallyReal.isReal
  let f : (d.I3 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    { toFun r w a j := star (∑ i, ((R.fr w)⁻¹).1 a i *
        ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))
      map_add' r s := funext fun w => funext fun a => funext fun j => by
        simp only [Pi.add_apply, Prod.fst_add, Complex.ofReal_add, add_mul, sum_add_distrib, mul_add, star_add]
      map_smul' c r := funext fun w => funext fun a => funext fun j => by
        simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul]
        conv_rhs => rw [show (c : ℂ) = star (c : ℂ) from (Complex.conj_ofReal c).symm, ← star_mul']
        congr 1; simp only [mul_sum]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro r hr0
    have hz (w : InfinitePlace F) : ∀ i j,
        ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l) = 0 := by
      let Z : Matrix (Fin d.m) (Fin d.n) ℂ := fun i j =>
        ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l)
      have h1 : ((R.fr w)⁻¹).1 * Z = 0 := by
        ext a j; have h' : star (∑ i, ((R.fr w)⁻¹).1 a i * Z i j) = 0 := congrFun (congrFun (congrFun hr0 w) a) j
        rw [star_eq_zero] at h'; rw [Matrix.mul_apply]; exact h'
      have h2 : Z = 0 := by
        rw [show Z = (R.fr w).1 * (((R.fr w)⁻¹).1 * Z) by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul],
          h1, Matrix.mul_zero]
      exact fun i j => congrFun₂ h2 i j
    funext ⟨i, j, l⟩
    refine Prod.ext (funext fun v => ?_)
      (funext fun v => absurd v.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (hr v.1)))
    have h := hz v.1 i j; rw [Fin.sum_univ_two] at h
    have hi := real_indep (detIm_ne_k d v.1) h
    rw [show (⟨v.1, hr v.1⟩ : {w : InfinitePlace F // w.IsReal}) = v from Subtype.ext rfl] at hi
    fin_cases l <;> [exact hi.1; exact hi.2]
  have hdim : Module.finrank ℝ (d.I3 → mixedEmbedding.mixedSpace F) =
      Module.finrank ℝ (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := by
    simp only [Module.finrank_pi_fintype, mixedEmbedding.finrank, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]; ring
  refine ⟨(LinearEquiv.ofBijective f ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩).toContinuousLinearEquiv,
    fun c w => funext fun a => funext fun j => ?_⟩
  show star (∑ i, ((R.fr w)⁻¹).1 a i * ∑ l : Fin 2,
      ((((InfiniteAdeleRing.ringEquiv_mixedSpace F (c (i, j, l)).1).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))) =
    star ((((R.fr w)⁻¹).1 * d.cw w (d.cmb c)) a j)
  rw [Matrix.mul_apply]; congr 1
  refine sum_congr rfl fun i _ => congrArg _ ?_
  show _ = piInf (d.B.emb w) (∑ l, c (i, j, l) ⊗ₜ[F] d.bs l); rw [map_sum]
  exact sum_congr rfl fun l _ => by
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    rfl
theorem cmb_add_k (d : SD_k σ) (c c' : d.I3 → AF F) : d.cmb (c + c') = d.cmb c + d.cmb c' := by
  ext i j; simp only [SD_k.cmb, Pi.add_apply, Matrix.add_apply, TensorProduct.add_tmul, sum_add_distrib]
theorem cmb_eq_k (d : SD_k σ) (c : d.I3 → AF F) (i : Fin d.m) (j : Fin d.n) :
    d.cmb c i j = ∑ k, c (i, j, k) • Algebra.TensorProduct.basis (AF F) d.bs k := by
  simp only [SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem crd_cmb'_k (d : SD_k σ) (c : d.I3 → AF F) : d.crd (d.cmb c) = c := crd_cmb_k d c
theorem cmb_crd_k (d : SD_k σ) (X : d.MxE) : d.cmb (d.crd X) = X := by
  ext i j; rw [cmb_eq_k]; exact (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)
theorem continuous_cmb_k (d : SD_k σ) : Continuous d.cmb := by
  obtain ⟨_, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [cmb_eq_k]; exact continuous_finsetSum _ fun k _ => (continuous_apply (i, j, k)).smul continuous_const
theorem continuous_crd_k (d : SD_k σ) : Continuous d.crd := by
  obtain ⟨_, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  exact continuous_pi fun k =>
    (IsModuleTopology.continuous_of_linearMap (((Finsupp.lapply k.2.2).comp
      (Algebra.TensorProduct.basis (AF F) d.bs).repr.toLinearMap) : AE F E →ₗ[AF F] AF F)).comp
    ((continuous_apply k.2.1).comp (continuous_apply k.1))
def cmbE_k (d : SD_k σ) : (d.I3 → AF F) ≃ₜ+ d.MxE :=
  ⟨⟨⟨d.cmb, d.crd, crd_cmb'_k d, cmb_crd_k d⟩, cmb_add_k d⟩, continuous_cmb_k d, continuous_crd_k d⟩
theorem mxTop_k (d : SD_k σ) : IsTopologicalAddGroup d.MxE ∧ LocallyCompactSpace d.MxE ∧
    SecondCountableTopology d.MxE ∧ BorelSpace d.MxE := by
  obtain ⟨_, _, _, _⟩ := (PositivityTheory.ThKCT.ideleTop F E).1; have : BorelSpace (AE F E) := ⟨rfl⟩
  exact ⟨inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E)),
    inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E)),
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E)),
    inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))⟩
theorem int_schM_k (d : SD_k σ) (ν : Measure d.MxE) (hν : ν.IsAddHaarMeasure) {f : d.MxE → ℂ}
    (hf : f ∈ d.schM) : Integrable f ν := by
  obtain ⟨_, _, _, _⟩ := mxTop_k d
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : BorelSpace (AF F) := ⟨rfl⟩; have : BorelSpace (d.I3 → AF F) := Pi.borelSpace
  let e : (d.I3 → AF F) ≃ᵐ d.MxE := (cmbE_k d).toHomeomorph.toMeasurableEquiv
  have : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (cmbE_k d).symm
  have h1 : Integrable (f ∘ e) (Measure.map e.symm ν) :=
    intSchA _ (congrArg (fun m => @MeasurableSpace.pi d.I3 (fun _ => AF F) fun _ => m) measAF_eq)
      _ inferInstance (Submodule.mem_comap.mp hf)
  have h2 := (integrable_map_equiv e f).2 h1; rwa [MeasurableEquiv.map_map_symm] at h2
theorem cw_add'_k (d : SD_k σ) (w : InfinitePlace F) (X Z : d.MxE) :
    d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
end KFock
namespace KSplitP
open SiegelEisensteinSeries.Grp
variable (d : SD_k σ)
theorem siegel_k {p : d.G} {t : d.Gn} (hp : IsPar p t) : ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ :=
  ⟨_, fun Φ hΦ => d.ok.dbl.weil.2.2 d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hp Φ hΦ⟩
theorem T_zero_k (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  unfold SD_k.T; congr 1; funext x; simp [Darboux.rho, schr, Matrix.zero_mul]
theorem loc_zero_k (R : RD_k d) (w : InfinitePlace F) : R.loc w 0 = 0 := by unfold RD_k.loc SD_k.cw; ext i j; simp
theorem iota_isPar_k (R : RD_k d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  have hn := d.ok.hn; obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set M := inFrame d.b (R.ι w q); set C := d.cw w M; have hw := R.at_w w q
  have e1 : dZ d.n R.ζ * C = fromBlocks C.toBlocks₁₁ C.toBlocks₁₂ (R.ζ • C.toBlocks₂₁) (R.ζ • C.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]; simp [dZ, fromBlocks_multiply]
  have e2 : mR q * dZ d.n R.ζ = fromBlocks (mR q).toBlocks₁₁ (R.ζ • (mR q).toBlocks₁₂) (mR q).toBlocks₂₁
      (R.ζ • (mR q).toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q)]; simp [dZ, fromBlocks_multiply]
  rw [e1, e2] at hw; obtain ⟨h11, -, h21, -⟩ := fromBlocks_inj.1 hw; rw [hq] at h21
  have hC21 : C.toBlocks₂₁ = 0 := (smul_eq_zero.1 h21).resolve_left (Krd.zeta_ne R.hζ)
  have hoff := R.off_f w q
  have hmem : R.ι w q ∈ parS σ d.Y d.b (siegelS hn) := (mem_parS_siegelS hn).2 fun i j =>
    Place.ad_ext d.cm d.B.emb (fun w' => by
      by_cases hw' : w' = w
      · subst hw'; simpa [toBlocks₂₁, C, SD_k.cw] using congrFun₂ hC21 i j
      · simpa [SD_k.cw, M] using congrFun₂ (R.off_w w w' q hw') (Sum.inr i) (Sum.inl j))
      (by simpa [M] using congrFun₂ hoff (Sum.inr i) (Sum.inl j))
  obtain ⟨t, hPt, hdet⟩ := isPar_of_mem_siegelS ht0 hn hmem; refine ⟨t, hPt, ?_⟩
  set N := M.toBlocks₁₁; set e := algebraMap (AF F) (AE F E) (finOne F)
  have hfinN : finOne F • N = finOne F • (1 : d.Mn) := Matrix.ext fun i j => by
    simpa [N, toBlocks₁₁, Matrix.one_apply] using congrFun₂ hoff (Sum.inl i) (Sum.inl j)
  have hidem : e * e = e := by rw [← map_mul, Krd.fin_idem]
  have hpow' : ∀ k : ℕ, e ^ (k + 1) = e := fun k => by
    induction k with | zero => simp | succ k ih => rw [pow_succ, ih, hidem]
  have hpow : e ^ d.n = e := by obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn); rw [hk]; exact hpow' k
  have hdetN : e * (N.det - 1) = 0 := by
    have h1 : (e • N).det = (e • (1 : d.Mn)).det := by rw [algebraMap_smul, algebraMap_smul, hfinN]
    rw [det_smul, det_smul, Fintype.card_fin, hpow, det_one, mul_one] at h1; rw [mul_sub, h1, mul_one, sub_self]
  have hat : ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1 ∈
      PositivityTheory.ThKG.CayleyTransformDarboux.atI F E := by
    rw [PositivityTheory.ThKG.CayleyTransformDarboux.mem_atI, hdet]; intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have eu : u = u * finOne F := Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (mul_one _).symm
    rw [Algebra.smul_def, eu, map_mul, mul_assoc, hdetN, mul_zero]
  rw [PositivityTheory.ThKG.CayleyTransformDarboux.absE_inf d.cm d.B.emb hat,
    Finset.prod_eq_single w (fun w' _ hne => by
      rw [hdet, RingHom.map_det, RingHom.mapMatrix_apply,
        show N.map (piInf (d.B.emb w')) = (d.cw w' M).toBlocks₁₁ from rfl, R.off_w w w' q hne,
        show (1 : Matrix d.N2 d.N2 ℂ).toBlocks₁₁ = 1 from by ext i j; simp [toBlocks₁₁, Matrix.one_apply],
        det_one, norm_one, one_pow])
      (fun h => absurd (Finset.mem_univ w) h), hdet, RingHom.map_det, RingHom.mapMatrix_apply,
    show N.map (piInf (d.B.emb w)) = C.toBlocks₁₁ from rfl, h11]
end KSplitP
namespace SD_k
variable (d : SD_k σ)
theorem inFrame_mul (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have hmul : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, hmul, mul_assoc]; rw [← mul_assoc (incM F d.b.1), Krd.bb_k d, one_mul]
theorem inFrame_one : inFrame d.b (1 : d.G) = 1 := by
  change incM F (d.b⁻¹).1 * 1 * incM F d.b.1 = 1; simpa only [mul_one] using Krd.bb'_k d
theorem inFrame_inj {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := by
  have hr (z : d.G) : mat2 z = incM F d.b.1 * inFrame d.b z * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← mul_assoc, Krd.bb_k d, one_mul]; rw [mul_assoc, Krd.bb_k d, mul_one]
  exact Subtype.ext (Units.ext (show mat2 x = mat2 y by rw [hr x, hr y, h]))
end SD_k
namespace RD_k
open RD
variable {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F)
theorem w_four {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 :=
  d.inFrame_inj <| by
    have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [d.inFrame_mul, d.inFrame_mul, d.inFrame_mul, hW, d.inFrame_one, wM_four _ (intUnit_sq ε)]
theorem w_four_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := w_four h
theorem cw_iota_pf (y : GR d.n) : d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  calc d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
        rw [← mul_assoc, Krd.dZ_inv_mul (Krd.zeta_ne R.hζ), one_mul]
    _ = _ := by rw [R.at_w w y, mul_assoc]
private theorem cw_wM {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b w₀) = wM d.n ((ε : ℤ) : ℂ) := by
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [hW]; ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [SD_k.cw, wM, hij]
private def nUpt (x : d.Mnc) (hx : xᴴ = x) : GR d.n :=
  ⟨⟨nU x, nU (-x), by simp [nU, fromBlocks_multiply, fromBlocks_one],
    by simp [nU, fromBlocks_multiply, fromBlocks_one]⟩,
    by show InG (nU x); simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, fromBlocks_multiply, hx]⟩
theorem oppositeUnipotent_weylConj {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) (y : GR d.n) (c : d.Mnc)
    (hc : cᴴ = c) (hy : mR y = nbLoc c) :
    ∃ y' : GR d.n, mR y' = nU ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) ∧ R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  have hζ0 := Krd.zeta_ne R.hζ; have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp [Complex.inv_I]
  set x := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c
  refine ⟨nUpt x (by rw [conjTranspose_smul, hc, hs]), rfl, d.inFrame_inj ?_⟩
  simp only [d.inFrame_mul]; apply Place.cw_ext_k d
  · intro w'; simp only [Krd.cw_mul_k d, cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (nUpt x _), hy, show mR (nUpt x _) = nU x from rfl,
        dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1; simp only [x, smul_smul]; congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]; simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, mul_one, hW, wM_four _ (intUnit_sq ε)]
end RD_k
namespace kfour
open SiegelEisensteinSeries.Grp
theorem sigma_sigma_of_good_k {B : Base F E} (hB : GoodK σ B) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := Classical.arbitrary _; exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
theorem coefEx_k : CoefEx_k := fun _ _ _ _ _ _ _ σ d => by
  have hσ := sigma_sigma_of_good_k d.ok.good; obtain ⟨_, _, _, _⟩ := nA_top hσ d.ok.frame
  obtain ⟨K, hK, hc⟩ := nF_cocompact hσ d.ok.frame
  obtain ⟨lam, 𝓖, hlam, h𝓖, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact d.nA_ d.nF_ K hK hc).1
  exact ⟨nbE σ d.Y d.b, lam, 𝓖, isNMap_nbE hσ d.ok.frame, hlam, h𝓖, h1⟩
theorem ratM_eq_k (d : SD_k σ) : d.ratM = ratMx F E d.m d.n := rfl
theorem auxiliaryExistence_holds : SiegelWeilDatumProperties := fun F E _ _ _ _ _ σ d => by
  obtain ⟨ν, 𝓕, hν, h𝓕, h1⟩ := exists_cov (F := F) (E := E) d.m d.n
  obtain ⟨i1, i2, i3, i4⟩ := doubled_group_topological_properties σ d.Y
  exact ⟨⟨ν, hν, 𝓕, h𝓕, h1⟩, exists_w d.ok.frame, i1, i2, i3, i4⟩
theorem fourierZero_k : FourierZero_k := fun F E _ _ _ _ _ σ d nb lam 𝓖 hc f hf hper hfc => funext fun x => by
  open GlobalTheory.ThK PositivityTheory.FTA.ZFC in
  have hσ := GlobalTheory.LeviLine.sigma_invol d.cm
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [d.cm.2.2.1]; norm_num)
  obtain ⟨ε, hε⟩ := d.ok.frame.1; obtain ⟨_, _, _, _⟩ := nA_top hσ d.ok.frame
  obtain ⟨K, hK, hcov⟩ := nF_cocompact hσ d.ok.frame
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF d.std
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) := IsModuleTopology.continuous_of_linearMap _
  have hker (β : d.nA_) : (∀ T : d.nF_, chr d.B.ψ d.b T β = 1) ↔ β ∈ d.nF_ := ⟨fun h => by
    refine (mem_nF_iff β).2 (rat_of_ker d.cm d.std ε β.1 ?_ fun T hT => ?_)
    · have e := (mem_nA_iff hσ hε β.1).1 β.2; simp only [nCond, AddSubgroup.mem_mk] at e; rw [e, Int.cast_smul_eq_zsmul]
    · have hm : incM F T ∈ d.nA_ := (mem_nA_iff hσ hε _).2 (by
        show (incM F T)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F T).map (cA σ))
        rw [Int.cast_smul_eq_zsmul, ← incM_map_cA]; ext i j; have := congrFun₂ hT i j
        simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] at this ⊢
        simp only [incM, Matrix.map_apply, this, map_neg, map_zsmul])
      exact h ⟨⟨incM F T, hm⟩, (mem_nF_iff _).2 ⟨T, rfl⟩⟩, fun hβF T => by
    obtain ⟨T₀, hT₀⟩ := (mem_nF_iff β).1 hβF; obtain ⟨T₁, hT₁⟩ := (mem_nF_iff T.1).1 T.2
    unfold chr; rw [hT₀, hT₁, ← PositivityTheory.FTA.ZFC.incM_mul, trace_incM_rat, ← map_neg]; exact d.std.2.1 _⟩
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero d.nA_ d.nF_ K hK hcov d.nF_
    (chr d.B.ψ d.b)
    (fun _ => hψ.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtypeVal).matrix_trace)).neg)
    (fun _ _ _ => by
      unfold chr
      rw [AddSubgroup.coe_add, Matrix.mul_add, trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul])
    (fun _ _ _ => by
      unfold chr; rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_mul, trace_add, map_add (f := _),
        neg_add, AddChar.map_add_eq_mul])
    (fun _ => by
      unfold chr; rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, Matrix.zero_mul, trace_zero, map_zero,
        neg_zero, AddChar.map_zero_eq_one])
    (fun _ _ => hψ.2.1 _) hker lam 𝓖 hc.2.1 hc.2.2.1 (fun β => f (nb β * x))
    (hf.comp ((nb_continuous hσ d.ok.frame hc.1).mul continuous_const))
    (fun γ hγ β => by show f (nb (γ + β) * x) = _; rw [nb_add hc.1, mul_assoc]; exact hper γ hγ _)
    (fun T => (integral_congr_ae (.of_forall fun _ => mul_comm _ _)).trans (hfc T x))
  simpa [nb_zero hc.1] using congrFun key 0
theorem fcBd'_core_k (d : SD_k σ) {nb lam 𝓖} (hc : d.CD nb lam 𝓖) (T : d.nF_) :
    ∃ K : Set d.nA_, IsCompact K ∧ ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) →
      ∀ y : d.G, (∀ β ∈ K, ‖f (nb β * y)‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T y‖ ≤ M := by
  obtain ⟨hnb, _, _, hvol⟩ := hc; obtain ⟨K, hK, hKc⟩ := nF_cocompact (sigma_sigma_of_good_k d.ok.good) d.ok.frame
  refine ⟨K, hK, fun f M hf y hM => ?_⟩
  have hbd (β : d.nA_) : ‖f (nb β * y) * d.B.ψ (-d.tt (T.1.1 * β.1))‖ ≤ M := by
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, (GlobalTheory.StdCharWeilDatum.isCharAF d.std).2.1 _, mul_one,
      show f (nb β * y) = f (nb (γ + β) * y) by rw [nb_add hnb, mul_assoc, hf _ (nb_rat hnb γ hγ)]]
    exact hM _ hk
  have h1 := norm_setIntegral_le_of_norm_le_const (by rw [hvol]; exact ENNReal.one_lt_top) (fun β _ => hbd β)
  rwa [show lam.real 𝓖 = 1 by simp [Measure.real, hvol], mul_one] at h1
theorem fcAll_core_k (d : SD_k σ) {nb lam 𝓖} (hc : d.CD nb lam 𝓖) (T : d.nF_) (x : d.G) :
    (∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ d.r2, ∀ g, f' (γ * g) = f' g) →
      fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T x = a * fc d.B.ψ d.b nb lam 𝓖 f T x + fc d.B.ψ d.b nb lam 𝓖 f' T x) ∧
    ∃ K : Set d.G, IsCompact K ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ K, ‖f y‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T x‖ ≤ M := by
  obtain ⟨hnb, _, _, hvol⟩ := hc; have hσ := sigma_sigma_of_good_k d.ok.good
  obtain ⟨_, _, _, _⟩ := nA_top hσ d.ok.frame; have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.std
  obtain ⟨K, hK, hKc⟩ := nF_cocompact hσ d.ok.frame
  set χ : d.nA_ → ℂ := fun β => d.B.ψ (-d.tt (T.1.1 * β.1))
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun β : d.nA_ => nb β * x := (nb_continuous hσ d.ok.frame hnb).mul continuous_const
  have hbd (f : d.G → ℂ) (M : ℝ) (hf : ∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g)
      (hM : ∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) (β : d.nA_) : ‖f (nb β * x) * χ β‖ ≤ M := by
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hψ.2.1 _, mul_one,
      show f (nb β * x) = f (nb (γ + β) * x) by rw [nb_add hnb, mul_assoc, hf _ (nb_rat hnb γ hγ)]]
    exact hM _ ⟨γ + β, hk, rfl⟩
  have hint (f : d.G → ℂ) (hfc : Continuous f) (hf : ∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) :
      IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam := by
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn
    exact Measure.integrableOn_of_bounded (M := M) hfin.ne
      ((hfc.comp hcm).mul (continuous_chr hψ.1 T.1.1)).aestronglyMeasurable (.of_forall (hbd f M hf hM))
  refine ⟨fun a f f' hfc hf'c hf hf' => ?_, (fun β => nb β * x) '' K, hK.image hcm, fun f M _ hf hM => ?_⟩
  · change ∫ β in 𝓖, (a • f + f') (nb β * x) * χ β ∂lam =
      a * ∫ β in 𝓖, f (nb β * x) * χ β ∂lam + ∫ β in 𝓖, f' (nb β * x) * χ β ∂lam
    rw [show (fun β : d.nA_ => (a • f + f') (nb β * x) * χ β) = fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β
        by funext β; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring,
      integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]
  · have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)
    rwa [show lam.real 𝓖 = 1 by simp [Measure.real, hvol], mul_one] at h1
theorem lamBd_k : LamBd_k := by
  rintro F E _ _ _ _ _ σ d _ ⟨nb, lam, 𝓖, T, x, hc, -, rfl⟩; exact fcAll_core_k d hc T x
end kfour
namespace KSing
open SiegelEisensteinSeries.Grp
namespace UnitaryGroupBasics
theorem inFrame_mul_k (d : SD_k σ) (x y : d.G) :
    inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := d.inFrame_mul x y
theorem inFrame_one_k (d : SD_k σ) : inFrame d.b (1 : d.G) = 1 := d.inFrame_one
theorem matrixRep_eq_frameConj_inFrame (d : SD_k σ) (x : d.G) :
    mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  simp only [inFrame, ← mul_assoc, Krd.bb_k d, one_mul]; rw [mul_assoc, Krd.bb_k d, mul_one]
theorem inFrame_inj_k (d : SD_k σ) {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := d.inFrame_inj h
theorem cw_mul_k (d : SD_k σ) (w : InfinitePlace F) {p q r : Type} [Fintype q]
    (X : Matrix p q (AE F E)) (Y : Matrix q r (AE F E)) : d.cw w (X * Y) = d.cw w X * d.cw w Y := Matrix.map_mul
theorem cw_one_k (d : SD_k σ) (w : InfinitePlace F) {p : Type} [Fintype p] [DecidableEq p] :
    d.cw w (1 : Matrix p p (AE F E)) = 1 := Krd.cw_one_k d w
theorem cw_transpose_k (d : SD_k σ) (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) :
    d.cw w Xᵀ = (d.cw w X)ᵀ := transpose_map
theorem cw_toBlocks₁₂_k (d : SD_k σ) (w : InfinitePlace F) (X : d.Mn2) :
    d.cw w X.toBlocks₁₂ = (d.cw w X).toBlocks₁₂ := rfl
theorem form_w_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (x : d.G) :
    (d.cw w (inFrame d.b x))ᵀ * Krd.Qc d.n R.ε * (d.cw w (inFrame d.b x)).map star = Krd.Qc d.n R.ε := by
  have hfr : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      incM F (fromBlocks 0 1 (((R.ε : ℤ) : E) • 1) 0 : Matrix d.N2 d.N2 E) := by
    rw [← R.hε, _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul', _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul', show incM F d.b.1ᵀ = (incM F d.b.1)ᵀ from transpose_map, Krd.dbl_incM_k,
      show incM F (d.b.1.map σ) = (incM F d.b.1).map (cA σ) by ext i j; simp only [incM, Matrix.map_apply, cA_inclR]]
  have h1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by rw [← transpose_mul, Krd.bb_k, transpose_one]
  have h2 : (incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ) = 1 := by
    rw [← mapc_mul, Krd.bb_k, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfa : (inFrame d.b x)ᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
      (inFrame d.b x).map (cA σ) = (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) := by
    unfold inFrame; rw [transpose_mul, transpose_mul, mapc_mul, mapc_mul]
    calc _ = (incM F d.b.1)ᵀ * (mat2 x)ᵀ * ((incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
            ((incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ)) * (mat2 x).map (cA σ) *
            (incM F d.b.1).map (cA σ) := by simp only [mul_assoc]
      _ = (incM F d.b.1)ᵀ * ((mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ)) *
            (incM F d.b.1).map (cA σ) := by rw [h1, h2, mul_one, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mat2]; rw [x.2]
  have hQ : d.cw w (incM F (fromBlocks 0 1 (((R.ε : ℤ) : E) • 1) 0 : Matrix d.N2 d.N2 E)) = Krd.Qc d.n R.ε := by
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [SD_k.cw, incM, Krd.Qc, hij, Matrix.smul_apply]
  have h := congrArg (d.cw w) hfa; rwa [hfr, cw_mul_k, cw_mul_k, hQ, cw_transpose_k, Place.cw_cA_k] at h
theorem cw_fromBlocks_k (d : SD_k σ) (w : InfinitePlace F) (B : d.Mn) :
    d.cw w (fromBlocks (1 : d.Mn) B (0 : d.Mn) 1) = fromBlocks (1 : d.Mnc) (d.cw w B) (0 : d.Mnc) 1 := by
  unfold SD_k.cw; rw [fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]
theorem piInf_trace_k (d : SD_k σ) (w : InfinitePlace F) (M : d.Mn) :
    piInf (d.B.emb w) M.trace = (d.cw w M).trace := by simp [SD_k.cw, Matrix.trace, map_sum]
open RD in
theorem cw_unip_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (u : GR d.n) (H : d.Mnc) (hu : mR u = nU H) :
    d.cw w (inFrame d.b (R.ι w u)) = fromBlocks 1 (R.ζ • H) 0 1 := by
  rw [R.cw_iota_pf w u, hu, dZ_conj_nU (Krd.zeta_ne R.hζ)]; rfl
end UnitaryGroupBasics
open UnitaryGroupBasics in
private theorem split_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (g : d.G) :
    ∃ (y : GR d.n) (x : d.G), g = R.ι w y * x ∧ ∀ y' : GR d.n, x * R.ι w y' = R.ι w y' * x := by
  have hζ0 := Krd.zeta_ne R.hζ; set M := d.cw w (inFrame d.b g)
  let y : GR d.n := mkGR _ (Krd.inG_conj R.hζ M (form_w_k d R w g))
  set x : d.G := (R.ι w y)⁻¹ * g
  refine ⟨y, x, (mul_inv_cancel_left _ _).symm, fun y' => ?_⟩
  have hyw : d.cw w (inFrame d.b (R.ι w y)) = M := by
    rw [R.cw_iota_pf w y]; show dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) * dZ d.n R.ζ = M
    simp only [Matrix.mul_assoc]; rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0,
      Matrix.one_mul]
  have hx : d.cw w (inFrame d.b x) = 1 := by
    have e1 : inFrame d.b (R.ι w y)⁻¹ * inFrame d.b (R.ι w y) = 1 := by
      rw [← inFrame_mul_k, inv_mul_cancel, inFrame_one_k]
    show d.cw w (inFrame d.b ((R.ι w y)⁻¹ * g)) = 1
    rw [inFrame_mul_k, cw_mul_k, show d.cw w (inFrame d.b g) = M from rfl, ← hyw, ← cw_mul_k, e1, cw_one_k]
  apply inFrame_inj_k d; rw [inFrame_mul_k d x, inFrame_mul_k d (R.ι w y')]
  refine Place.cw_ext_k d (fun w' => ?_)
    (by rw [fin_mul, fin_mul, R.off_f w y', ← fin_mul, ← fin_mul, mul_one, one_mul])
  rw [cw_mul_k, cw_mul_k]
  by_cases h : w' = w
  · subst h; rw [hx, one_mul, mul_one]
  · rw [R.off_w w w' y' h, one_mul, mul_one]
theorem nilpotentMap_add (d : SD_k σ) : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good_k d.ok.good
theorem nb_add_k (d : SD_k σ) {nb : d.nA_ → d.G} (h : IsNMap d.b nb) (β β' : d.nA_) : nb (β + β') = nb β * nb β' :=
  kfour.nb_add h β β'
theorem nb_rat_k (d : SD_k σ) {nb : d.nA_ → d.G} (h : IsNMap d.b nb) {β : d.nA_} (hβ : β ∈ d.nF_) : nb β ∈ d.r2 :=
  kfour.nb_rat h β hβ
private theorem chi_props (d : SD_k σ) (T : d.nF_) :
    Continuous (fun β : d.nA_ => d.B.ψ (-d.tt (T.1.1 * β.1))) ∧
    (∀ l ∈ d.nF_, d.B.ψ (-d.tt (T.1.1 * l.1)) = 1) ∧
    (∀ β β' : d.nA_, d.B.ψ (-d.tt (T.1.1 * (β + β').1)) =
      d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (-d.tt (T.1.1 * β'.1))) :=
  ⟨d.std.1.comp ((IsModuleTopology.continuous_of_linearMap (R := AF F)
      (Algebra.trace (AF F) (AE F E))).comp (continuous_const.matrix_mul continuous_subtypeVal).matrix_trace).neg,
   fun l hl => by
    obtain ⟨T₀, hT₀⟩ := (kfour.mem_nF_iff T.1).1 T.2; obtain ⟨l₀, hl₀⟩ := (kfour.mem_nF_iff l).1 hl
    rw [SD_k.tt, hT₀, hl₀, ← kfour.incM_mul']; exact psi_rat d.std.2.1 (T₀ * l₀),
   fun _ _ => by
    rw [SD_k.tt, SD_k.tt, SD_k.tt, AddSubgroup.coe_add, Matrix.mul_add, trace_add, map_add (f := _), neg_add,
      AddChar.map_add_eq_mul]⟩
theorem fc_shift_k (d : SD_k σ) {nb : d.nA_ → d.G} {lam : Measure d.nA_} {𝓖 : Set d.nA_} (hCD : d.CD nb lam 𝓖)
    (f : d.G → ℂ) (hinv : ∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) (T : d.nF_) (β₁ : d.nA_) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * fc d.B.ψ d.b nb lam 𝓖 f T z := by
  obtain ⟨hN, hHaar, hD, -⟩ := hCD; obtain ⟨_, _, _, _⟩ := kfour.nA_top (nilpotentMap_add d) d.ok.frame
  have : lam.IsAddHaarMeasure := hHaar
  have : VAddInvariantMeasure d.nF_ d.nA_ lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  obtain ⟨-, hcp, hca⟩ := chi_props d T
  set χ : d.nA_ → ℂ := fun β => d.B.ψ (-d.tt (T.1.1 * β.1)); set u : d.nA_ → ℂ := fun β => f (nb β * z) * χ β
  have hper (γ : d.nF_) (x : d.nA_) : u (γ +ᵥ x) = u x := by
    show f (nb (γ.1 + x) * z) * χ (γ.1 + x) = _; simp only [χ]
    rw [hca, hcp _ γ.2, one_mul, nb_add_k d hN, mul_assoc, hinv _ (nb_rat_k d hN γ.2)]
  have hc : d.B.ψ (d.tt (T.1.1 * β₁.1)) * χ β₁ = 1 := by
    simp only [χ]; rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have eL : fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * ∫ β in 𝓖, u (β₁ + β) ∂lam := by
    unfold fc; rw [← integral_const_mul]; congr 1; funext β
    change f (nb β * (nb β₁ * z)) * χ β = d.B.ψ (d.tt (T.1.1 * β₁.1)) * (f (nb (β₁ + β) * z) * χ (β₁ + β))
    simp only [χ]; rw [← mul_assoc, ← nb_add_k d hN, add_comm β₁ β, hca β β₁]
    linear_combination (-(f (nb (β + β₁) * z) * χ β)) * hc
  rw [eL]; congr 1
  have h2 : IsAddFundamentalDomain d.nF_ ((fun β => -β₁ + β) ⁻¹' 𝓖) lam :=
    hD.preimage_of_equiv (measurePreserving_add_left lam (-β₁)).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ x => by show -β₁ + (γ.1 + x) = γ.1 + (-β₁ + x); abel
  calc ∫ β in 𝓖, u (β₁ + β) ∂lam
      = ∫ β in (fun β : d.nA_ => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖), u (β₁ + β) ∂lam := by
        rw [show (fun β : d.nA_ => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖) = 𝓖 by ext β; simp]
    _ = ∫ β in (fun β => -β₁ + β) ⁻¹' 𝓖, u β ∂lam :=
        (measurePreserving_add_left lam β₁).setIntegral_preimage_emb (measurableEmbedding_addLeft β₁) u _
    _ = ∫ β in 𝓖, u β ∂lam := h2.setIntegral_eq hD hper
open UnitaryGroupBasics in
private theorem nbw_charW (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) {nb : d.nA_ → d.G} (h : IsNMap d.b nb)
    (nr : RM d → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x)) :
    ∃ β : RM d → d.nA_, Continuous β ∧ (∀ x, R.ι w (nr x) = nb (β x)) ∧
      ∀ T : d.nF_, ∃ β' : d.Mnc, β'.IsHermitian ∧ (T.1.1.det = 0 → β'.det = 0) ∧
        ∀ x, d.B.ψ (d.tt (T.1.1 * (β x).1)) = eTr β' x := by
  have hP (x : RM d) : inFrame d.b (R.ι w (nr x)) = fromBlocks 1 (inFrame d.b (R.ι w (nr x))).toBlocks₁₂ 0 1 :=
    Place.cw_ext_k d (fun u => by
      rw [cw_fromBlocks_k, show d.cw u (inFrame d.b (R.ι w (nr x))).toBlocks₁₂ =
        (d.cw u (inFrame d.b (R.ι w (nr x)))).toBlocks₁₂ from rfl]
      by_cases hu : u = w
      · subst hu; rw [cw_unip_k d R u (nr x) _ (hnr x), Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u (nr x) hu, toBlocks₁₂_one, fromBlocks_one]) (by
        rw [fromBlocks_smul, fin_toBlocks₁₂, R.off_f w (nr x), ← fin_toBlocks₁₂, toBlocks₁₂_one, smul_zero,
          ← fromBlocks_one, fromBlocks_smul, smul_zero])
  let β : RM d → d.nA_ :=
    fun x => ⟨(inFrame d.b (R.ι w (nr x))).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w (nr x), hP x⟩⟩
  have hβ (x : RM d) : R.ι w (nr x) = nb (β x) := inFrame_inj_k d (by rw [h]; exact hP x)
  have hβc : Continuous β := by
    have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    have hc : Continuous fun x => inFrame d.b (R.ι w (nr x)) :=
      ((continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtypeVal)).matrix_mul
        continuous_const).comp ((R.cont w).comp (continuous_nr nr hnr))
    exact Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j =>
      hc.matrix_elem (Sum.inl i) (Sum.inr j)) _
  refine ⟨β, hβc, hβ, fun T => ?_⟩
  have hB (x : RM d) : inFrame d.b (R.ι w (nr x)) = fromBlocks 1 (β x).1 0 1 := by rw [hβ x, h]
  have hBw (x : RM d) : d.cw w (β x).1 = R.ζ • herm x := by
    have e := cw_unip_k d R w (nr x) _ (hnr x); rw [hB x, cw_fromBlocks_k] at e; exact (fromBlocks_inj.1 e).2.1
  have hBu (x : RM d) (u : InfinitePlace F) (hu : u ≠ w) : d.cw u (β x).1 = 0 := by
    have e := R.off_w w u (nr x) hu; rw [hB x, cw_fromBlocks_k, ← fromBlocks_one] at e; exact (fromBlocks_inj.1 e).2.1
  have hBf (x : RM d) : finOne F • (β x).1 = 0 := by
    have e := R.off_f w (nr x); rw [hB x, fromBlocks_smul, ← fromBlocks_one, fromBlocks_smul] at e
    exact (fromBlocks_inj.1 e).2.1.trans (smul_zero _)
  set Tw := d.cw w T.1.1
  have hT : Twᵀ + ((R.ε : ℤ) : ℂ) • Tw.map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩; have e := form_w_k d R w x; rw [hx, cw_fromBlocks_k] at e
      simp [Krd.Qc, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply] at e; rwa [add_comm]
    · ext i j; simp [SD_k.cw]
    · intro a b _ _ ha hb; ext i j; have ea := congrFun₂ ha i j; have eb := congrFun₂ hb i j
      simp [SD_k.cw] at ea eb ⊢; linear_combination ea + eb
    · intro a _ ha; ext i j
      have ea := congrFun₂ ha i j; simp [SD_k.cw] at ea ⊢; linear_combination -ea
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j; have e := congrFun₂ hT j i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  refine ⟨-(2 : ℂ) • (R.ζ • Tw), by rw [Matrix.IsHermitian, conjTranspose_smul, hAh]; simp, fun h0 => ?_, fun x => ?_⟩
  · have hd : Tw.det = 0 := by
      rw [show Tw.det = ((piInf (d.B.emb w)).mapMatrix T.1.1).det from rfl, ← RingHom.map_det, h0, map_zero]
    rw [det_smul, det_smul, hd]; simp
  · have hf : finOne F • (T.1.1 * (β x).1).trace = 0 := by
      rw [← trace_smul, ← Matrix.mul_smul, hBf x, Matrix.mul_zero, trace_zero]
    have hw (u : InfinitePlace F) (hu : u ≠ w) : piInf (d.B.emb u) (T.1.1 * (β x).1).trace = 0 := by
      rw [piInf_trace_k, cw_mul_k, hBu x u hu, Matrix.mul_zero, trace_zero]
    have hw' : piInf (d.B.emb w) (T.1.1 * (β x).1).trace = ((R.ζ • Tw) * herm x).trace := by
      rw [piInf_trace_k, cw_mul_k, hBw x, Matrix.mul_smul, Matrix.smul_mul]
    have hreal : ((((R.ζ • Tw) * herm x).trace).re : ℂ) = ((R.ζ • Tw) * herm x).trace :=
      Complex.conj_eq_iff_re.1 (by
        show star ((R.ζ • Tw * herm x).trace) = _
        rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hAh, herm_conjTranspose', Matrix.trace_mul_comm])
    unfold SD_k.tt eTr
    rw [Place.psi_trace_at d.std d.cm d.B.emb w _ hf hw, hw',
      show (-(2 : ℂ) • (R.ζ • Tw)) * herm x = -(2 : ℂ) • ((R.ζ • Tw) * herm x) from Matrix.smul_mul _ _ _,
      trace_smul, smul_eq_mul]
    generalize ((R.ζ • Tw) * herm x).trace = c at hreal ⊢
    congr 1; push_cast; rw [hreal]; ring
private theorem fc_avg_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (hG : IsTopologicalGroup d.G)
    {nb : d.nA_ → d.G} {lam : Measure d.nA_} {𝓖 : Set d.nA_} (hCD : d.CD nb lam 𝓖)
    (f : d.G → ℂ) (hf : Continuous f) (hinv : ∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g)
    (ψ₀ : RM d → ℂ) (hψc : Continuous ψ₀) (hψs : HasCompactSupport ψ₀)
    (nr : RM d → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (β : RM d → d.nA_) (hβ : ∀ x, R.ι w (nr x) = nb (β x)) (T : d.nF_) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      fc d.B.ψ d.b nb lam 𝓖 f T z * ∫ x, ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1)) := by
  have := hG; obtain ⟨hχc, hχp, hχa⟩ := chi_props d T
  set χ : d.nA_ → ℂ := fun β₀ => d.B.ψ (-d.tt (T.1.1 * β₀.1))
  set U : d.nA_ × d.G → ℂ := fun p => f (nb p.1 * p.2) * χ p.1
  have hιr : Continuous fun x => R.ι w (nr x) * z := ((R.cont w).comp (cont_nr nr hnr)).mul continuous_const
  have hUc : Continuous U := (hf.comp (((kfour.nb_continuous (nilpotentMap_add d) d.ok.frame hCD.1).comp
    continuous_fst).mul continuous_snd)).mul (hχc.comp continuous_fst)
  obtain ⟨K, hK, hKx⟩ := kfour.nF_cocompact (nilpotentMap_add d) d.ok.frame
  obtain ⟨M, hM⟩ := (hK.prod (hψs.isCompact.image hιr)).exists_bound_of_continuousOn hUc.continuousOn
  have hM' (β₀ : d.nA_) (y : d.G) (hy : y ∈ (fun x => R.ι w (nr x) * z) '' tsupport ψ₀) : ‖U (β₀, y)‖ ≤ M := by
    obtain ⟨γ, hγ, hγK⟩ := hKx β₀
    rw [show U (β₀, y) = U (γ + β₀, y) by
      simp only [U, χ]; rw [hχa, hχp _ hγ, one_mul, nb_add_k d hCD.1, mul_assoc, hinv _ (nb_rat_k d hCD.1 hγ)]]
    exact hM _ ⟨hγK, hy⟩
  have : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ]; erw [hCD.2.2.2]; exact ENNReal.one_lt_top⟩
  have eL : fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      ∫ β₀, ∫ x, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂volume ∂(lam.restrict 𝓖) := by
    refine integral_congr_ae (.of_forall fun β₀ => ?_)
    change (∫ x, f (R.ι w (nr x) * (nb β₀ * z)) * ψ₀ x) * χ β₀ = _
    rw [← integral_mul_const]; refine integral_congr_ae (.of_forall fun x => ?_)
    change f (R.ι w (nr x) * (nb β₀ * z)) * ψ₀ x * χ β₀ = f (nb β₀ * (R.ι w (nr x) * z)) * χ β₀ * ψ₀ x
    rw [show R.ι w (nr x) * (nb β₀ * z) = nb β₀ * (R.ι w (nr x) * z) by
      rw [hβ x, ← mul_assoc, ← nb_add_k d hCD.1, add_comm, nb_add_k d hCD.1, mul_assoc]]; ring
  have hint : Integrable (Function.uncurry fun (β₀ : d.nA_) (x : RM d) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) ((lam.restrict 𝓖).prod volume) := by
    refine Integrable.mono' ((integrable_const M).mul_prod (hψc.norm.integrable_of_hasCompactSupport hψs.norm))
      (kfour.aesm_of_continuous (nilpotentMap_add d) d.ok.frame lam 𝓖
        ((hUc.comp (continuous_fst.prodMk (hιr.comp continuous_snd))).mul (hψc.comp continuous_snd)))
      (.of_forall fun p => ?_)
    show ‖U (p.1, R.ι w (nr p.2) * z) * ψ₀ p.2‖ ≤ M * ‖ψ₀ p.2‖; rw [norm_mul]
    by_cases hx : p.2 ∈ tsupport ψ₀
    · exact mul_le_mul_of_nonneg_right (hM' p.1 _ ⟨p.2, hx, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  rw [eL, integral_integral_swap hint]
  have e2 (x : RM d) : ∫ β₀, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂(lam.restrict 𝓖) =
      fc d.B.ψ d.b nb lam 𝓖 f T z * (ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1))) := by
    rw [integral_mul_const, show ∫ β₀, U (β₀, R.ι w (nr x) * z) ∂(lam.restrict 𝓖) =
      fc d.B.ψ d.b nb lam 𝓖 f T (nb (β x) * z) by rw [hβ x]; rfl, fc_shift_k d hCD f hinv T (β x) z]; ring
  simp_rw [e2]; rw [integral_const_mul]
theorem lamSing_of_k (hCE : CoefEx_k) (hFZ : FourierZero_k) (hDW : DenseW_k)
    (hAux : SiegelWeilDatumProperties) : LamSing_k := fun F E _ _ _ _ _ σ d R w f hf hinv hL ψ₀ hψ nr hnr g a b => by
  obtain ⟨-, -, hG, hLC, -, hSC⟩ := hAux F E σ d; have := hG; have := hLC; have := hSC
  obtain ⟨nb, lam, 𝓖, hCD⟩ := hCE F E σ d; obtain ⟨β, -, hβ, hchar⟩ := nbw_charW d R w hCD.1 nr hnr
  have h0 (z : d.G) : ∫ x, f (R.ι w (nr x) * z) * ψ₀ x = 0 := by
    have hc : Continuous (Function.uncurry fun (y : d.G) (x : RM d) => f (R.ι w (nr x) * y) * ψ₀ x) :=
      (hf.comp (((R.cont w).comp ((cont_nr nr hnr).comp continuous_snd)).mul continuous_fst)).mul
        (hψ.1.comp continuous_snd)
    have hφc : Continuous fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x :=
      (continuous_parametric_integral_of_continuous (μ := (volume : Measure (RM d))) hc hψ.2.1.isCompact).congr
        fun _ => setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => by
          rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have hφinv (β₀ : d.nA_) (hβ₀ : β₀ ∈ d.nF_) (z : d.G) :
        (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) (nb β₀ * z) =
        (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) z := by
      dsimp only; congr 1; funext x
      rw [hβ x, ← mul_assoc, ← nb_add_k d hCD.1, add_comm, nb_add_k d hCD.1, mul_assoc, hinv _ (nb_rat_k d hCD.1 hβ₀)]
    have hφco (T : d.nF_) (z : d.G) :
        fc d.B.ψ d.b nb lam 𝓖 (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z = 0 := by
      rw [fc_avg_k d R w hG hCD f hf hinv ψ₀ hψ.1 hψ.2.1 nr hnr β hβ T z]
      by_cases hT : T.1.1.det = 0
      · obtain ⟨β', hβ'h, hβ'd, hβ'e⟩ := hchar T; simp_rw [hβ'e]; rw [hψ.2.2 β' hβ'h (hβ'd hT), mul_zero]
      · rw [show fc d.B.ψ d.b nb lam 𝓖 f T z = 0 from hL _ ⟨nb, lam, 𝓖, T, z, hCD, hT, rfl⟩, zero_mul]
    exact congrFun (hFZ F E σ d nb lam 𝓖 hCD _ hφc hφinv hφco) z
  obtain ⟨y, x, rfl, hx⟩ := split_k d R w g
  let Fz : d.G → M2 d.n → ℂ := fun h M => f (R.ι w (toGR' M) * h)
  let Γ : Set (M2 d.n) := {M | ∃ y' : GR d.n, M = mR y' ∧ ∃ γ ∈ d.r2, ∃ x' : d.G, γ = x' * R.ι w y' ∧
    ∀ y'' : GR d.n, x' * R.ι w y'' = R.ι w y'' * x'}
  have key := LVs.twoSided d.n d.G Fz Γ (fun h => by
    rw [continuousOn_iff_continuous_domRestrict, show Set.domRestrict {g | InG g} (Fz h) =
      fun p : {M : M2 d.n | InG M} => f (R.ι w (mkG p.1 p.2) * h) from
        funext fun p => by show f (R.ι w (toGR' p.1) * h) = _; rw [toGR'_of p.2]]
    exact hf.comp (((R.cont w).comp continuous_mkG).mul continuous_const))
    (by rintro _ ⟨y', rfl, -⟩; exact y'.2)
    (fun M hM => mem_closure_iff.2 fun U hU hMU => by
      obtain ⟨γ, hγ, y', hy'O, x', hγx, hx'⟩ := hDW F E σ d R w (mkG M hM) (mR ⁻¹' U) (hU.preimage continuous_mR) hMU
      exact ⟨mR y', hy'O, y', rfl, γ, hγ, x', hγx, hx'⟩)
    (by
      rintro _ ⟨y', rfl, γ, hγ, x', hγx, hx'⟩ h; refine ⟨x'⁻¹ * h, fun g' hg' => ?_⟩
      have hy' : R.ι w y' = γ * x'⁻¹ := by rw [hγx, hx' y', mul_inv_cancel_right]
      have hc : x'⁻¹ * R.ι w (mkG g' hg') = R.ι w (mkG g' hg') * x'⁻¹ := (Commute.inv_left (hx' _)).eq
      simp only [Fz]
      rw [show mR y' * g' = mR (y' * mkG g' hg') from rfl, toGR'_mR, toGR'_of hg', map_mul, hy', mul_assoc,
        mul_assoc, hinv γ hγ, ← mul_assoc, hc, mul_assoc])
    ψ₀ hψ.1 hψ.2.1 (fun h g' hg' => by
      have e (t : RM d) : Fz h (nU (herm t) * g') = f (R.ι w (nr t) * (R.ι w (mkG g' hg') * h)) := by
        simp only [Fz]; rw [show nU (herm t) * g' = mR (nr t * mkG g' hg') by rw [mR_mul', hnr, mR_mkG],
          toGR'_mR, map_mul, mul_assoc]
      simp_rw [e]; exact h0 _) x (mR (y * a)) (mR b) (y * a).2 b.2
  have e (t : RM d) : R.ι w y * x * R.ι w (a * nr t * b) = R.ι w (y * a * nr t * b) * x := by
    rw [mul_assoc, hx, ← mul_assoc]; simp only [map_mul, mul_assoc]
  have e' (t : RM d) : Fz x (mR (y * a) * nU (herm t) * mR b) = f (R.ι w (y * a * nr t * b) * x) := by
    simp only [Fz]
    rw [show mR (y * a) * nU (herm t) * mR b = mR (y * a * nr t * b) by rw [← hnr, ← mR_mul', ← mR_mul'], toGR'_mR]
  simp_rw [e]; simp_rw [e'] at key; exact key
end KSing
open RD in
theorem RD_k.isW_eps {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ε = R.ε :=
  eps_of_unit d.ok.hn ε R.ε (by simpa [RD_k.cw_wM h w] using KSing.UnitaryGroupBasics.form_w_k d R w w₀)
end PositivityTheory.SiegelWeilFormula
end
