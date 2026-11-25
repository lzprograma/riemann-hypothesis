module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleInfIdDetLe
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.InvMulVecScalarMul

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  simp only [absD, map_mul, Positive.val_mul]

theorem absD_pos (g : GA F 2) : 0 < absD g := EisensteinIntegrability.absD_pos g

theorem ideleModule_infId (d : (UpperTheory.V.TR.Rinf F)ˣ) :
    (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F d) : ℝ) = ∏ v, |(d : UpperTheory.V.TR.Rinf F) v| :=
  eisensteinGrowth.ideleModule_infId d

theorem absD_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    absD (UpperTheory.V.TR.infGL F 2 y) = ∏ v, |(Matrix.det (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) v| := by
  rw [absD, UpperTheory.V.TR.det_infGL, eisensteinGrowth.ideleModule_infId]
  rfl

theorem measurableEmbedding_expPos : MeasurableEmbedding expPos :=
  expPosHomeomorph.measurableEmbedding

instance sigmaFinite_posRealMeasure : SigmaFinite posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  exact measurableEmbedding_expPos.sigmaFinite_map

theorem measurableSet_ge_one : MeasurableSet {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} :=
  measurable_subtype_coe measurableSet_Ici

theorem measurableSet_lt_one : MeasurableSet {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} :=
  measurable_subtype_coe measurableSet_Iio

theorem integrableOn_ge_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) {t | 1 ≤ (t : ℝ)} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} = Set.Ici 0 := by
    ext x; simp [Real.one_le_exp_iff]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) ∘ expPos =
      fun x => Real.exp ((1 - (r : ℝ)) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hneg : (1 - (r : ℝ)) < 0 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Ioi hneg 0).congr_set_ae Ioi_ae_eq_Ici.symm

theorem integrableOn_lt_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) {t | (t : ℝ) < 1} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} = Set.Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, coe_expPos, Set.mem_Iio]
    rw [← Real.exp_zero, Real.exp_lt_exp]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) ∘ expPos =
      fun x => Real.exp (((r : ℝ) - 1) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hpos : 0 < ((r : ℝ) - 1) := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Iic hpos 0).mono_set Set.Iio_subset_Iic_self

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
