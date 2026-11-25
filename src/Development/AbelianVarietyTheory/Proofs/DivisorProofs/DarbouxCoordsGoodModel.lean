module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOpBOfMemClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.RingTheory.PiTensorProduct

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormula, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflection, Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductChar, Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel, Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormula =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormula", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegral\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStable\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks\npublic import Mathlib.Analysis.Calculus.BumpFunction.Basic\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.WeylMeas

open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_meas : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ],
    ∃ μ : Measure (κ → AF F), μ.IsAddRightInvariant ∧
      ∀ (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), Continuous g →
        Integrable g (measI F κ) → (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
        Integrable (fun x => g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i))) μ ∧
        ∫ x, g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ =
          (∫ z, g z ∂(measI F κ)) * ∏ᶠ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) := by
  intro F _ _ ψ hψ hunr hne κ _
  classical
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI hB : ∀ v : Pl (F := F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI hSC : ∀ v : Pl (F := F), SecondCountableTopology (Fv F v) := fun v => GlobalTheory.SplitWeil.secondCountable _
  haveI hH : ∀ v : Pl (F := F), (measV ψ v).IsAddHaarMeasure := fun v => (isSelfDualFor_measV ψ hψ.1 v (hne v)).1
  haveI : (measI F κ).IsAddHaarMeasure := measI_isAddHaar F κ
  have hOint : ∀ v : Pl (F := F), (v.adicCompletionIntegers F : Set (Fv F v)) =
      ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := fun v => by
    ext x; exact (GlobalTheory.WeylFour.IndOSelf.mem_int_iff x).symm
  have hOc : ∀ v : Pl (F := F), IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isCompact_int _
  have hOo : ∀ v : Pl (F := F), IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isOpen_int _
  have hOpi : ∀ v : Pl (F := F), {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
      Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    ext x; simp
  have hOm : ∀ v : Pl (F := F), MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun v => by
    rw [hOpi v]; exact MeasurableSet.univ_pi fun _ => (hOo v).measurableSet
  set c : Pl (F := F) → ℝ≥0∞ := fun v =>
    (Measure.pi fun _ : κ => measV ψ v) {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} with hcdef
  have hcpi : ∀ v, c v = ∏ _i : κ, measV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    simp only [c]; rw [hOpi v, Measure.pi_pi]
  have hc0 : ∀ v, c v ≠ 0 := fun v => by
    rw [hcpi v]
    exact Finset.prod_ne_zero_iff.2 fun _ _ =>
      ((hOo v).measure_pos (measV ψ v) ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne'
  have hct : ∀ v, c v ≠ ⊤ := fun v => by
    rw [hcpi v]
    exact ENNReal.prod_ne_top fun _ _ => (hOc v).measure_lt_top.ne
  have hc1 : ∀ v, PsiUnr ψ v → c v = 1 := fun v hv => by
    have h1 := (GlobalTheory.WeylFour.IndOSelf.isUnitVol_measV ψ v hv).2
    rw [← hOint v] at h1
    rw [hcpi v, h1, Finset.prod_const_one]
  set μv : ∀ v : Pl (F := F), Measure (κ → Fv F v) := fun v => (c v)⁻¹ • Measure.pi fun _ : κ => measV ψ v with hμvdef
  haveI hμvH : ∀ v, (μv v).IsAddHaarMeasure := fun v =>
    Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (hct v)) (ENNReal.inv_ne_top.2 (hc0 v))
  have hμv1 : ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := fun v => by
    simp only [μv]
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (hc0 v) (hct v)
  have hpi : ∀ v, (Measure.pi fun _ : κ => measV ψ v) = c v • μv v := fun v => by
    simp only [μv, smul_smul, ENNReal.mul_inv_cancel (hc0 v) (hct v), one_smul]
  obtain ⟨c₀, hc₀, hform⟩ := GlobalTheory.AdelicHaarPure.integral_pure_haar F κ (Measure.addHaar : Measure (κ → AF F))
    (measI F κ) μv hμv1

  have hind1 : ∀ v, ∫ x, GlobalTheory.RatWeilOp.ind κ v x ∂(μv v) = 1 := fun v => by
    have := integral_indicator_const (μ := μv v) (1 : ℂ) (hOm v)
    simpa [GlobalTheory.RatWeilOp.ind, Measure.real, Pi.one_def, hμv1 v] using this

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbcs : HasCompactSupport (fun z => b z) := b.hasCompactSupport
  have hf₀c : Continuous (fun z => ((b z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp b.continuous
  have hf₀cs : HasCompactSupport (fun z => ((b z : ℝ) : ℂ)) := hbcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hf₀i : Integrable (fun z => ((b z : ℝ) : ℂ)) (measI F κ) := hf₀c.integrable_of_hasCompactSupport hf₀cs
  have hBpos : 0 < ∫ z, b z ∂(measI F κ) :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := measI F κ) (x := 0) hbcs (fun z => b.nonneg)
      (by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; exact one_ne_zero)
  have hfam0 : GlobalTheory.RatWeilOp.IsFam (fun v : Pl F => GlobalTheory.RatWeilOp.ind κ v) :=
    ⟨fun v => GlobalTheory.WeylFour.IndOSelf.indO_mem_SB v κ, Filter.Eventually.of_forall fun v => rfl⟩
  obtain ⟨-, h0⟩ := hform (fun z => ((b z : ℝ) : ℂ)) _ hf₀c hf₀i hfam0
  rw [finprod_congr hind1, finprod_one, mul_one, integral_complex_ofReal] at h0
  set H : (κ → AF F) → ℂ := fun x => ((b (fun i => evI F (x i)) : ℝ) : ℂ) *
    ∏ᶠ v, GlobalTheory.RatWeilOp.ind κ v (fun i => evFin F v (x i)) with hHdef
  have key : ∀ z w : ℂ, (z.im = 0 ∧ 0 ≤ z.re) → (w.im = 0 ∧ 0 ≤ w.re) → ((z * w).im = 0 ∧ 0 ≤ (z * w).re) := by
    rintro z w ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨by rw [Complex.mul_im, h1, h3]; simp, by rw [Complex.mul_re, h1, h3]; simpa using mul_nonneg h2 h4⟩
  have hP : ∀ x, (H x).im = 0 ∧ 0 ≤ (H x).re := by
    intro x
    refine key _ _ ⟨by simp, by simpa using b.nonneg⟩ ?_
    refine finprod_induction (fun z : ℂ => z.im = 0 ∧ 0 ≤ z.re) ⟨by simp, by simp⟩ key (fun v => ?_)
    by_cases h : (fun i => evFin F v (x i)) ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F}
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_mem h]
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_notMem h]
  have hHr : H = fun x => (((H x).re : ℝ) : ℂ) := funext fun x => Complex.ext (by simp) (by simp [(hP x).1])
  have hL : ∫ x, H x ∂(Measure.addHaar : Measure (κ → AF F)) =
      ((∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) : ℝ) : ℂ) := by
    conv_lhs => rw [hHr]
    exact integral_complex_ofReal
  have hLnn : 0 ≤ ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) := integral_nonneg fun x => (hP x).2
  set L := ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) with hLdef
  set B := ∫ z, b z ∂(measI F κ) with hBdef
  have hc₀eq : c₀ = ((L / B : ℝ) : ℂ) := by
    have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hBpos.ne'
    rw [Complex.ofReal_div, eq_div_iff hB0, ← hL, ← h0]
  set t := L / B with htdef
  have ht0 : t ≠ 0 := fun h => hc₀ (by rw [hc₀eq, h, Complex.ofReal_zero])
  have htpos : 0 < t := lt_of_le_of_ne (div_nonneg hLnn hBpos.le) (Ne.symm ht0)

  obtain ⟨T, hT⟩ : ∃ T : Finset (Pl (F := F)), ∀ v ∉ T, PsiUnr ψ v :=
    ⟨(Filter.eventually_cofinite.1 hunr).toFinset, fun v hv => by simpa using hv⟩
  set Cr : ℝ := ∏ v ∈ T, (c v).toReal with hCrdef
  have hCr : 0 ≤ Cr := Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg
  refine ⟨ENNReal.ofReal (Cr / t) • Measure.addHaar, inferInstance, fun g φ hgc hgi hSB hev => ?_⟩
  have hfam : GlobalTheory.RatWeilOp.IsFam φ := ⟨hSB, hev⟩
  obtain ⟨hI, hE⟩ := hform g φ hgc hgi hfam
  refine ⟨hI.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  have hloc : ∀ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) = ((c v).toReal : ℂ) * ∫ z, φ v z ∂(μv v) :=
    fun v => by rw [hpi v, integral_smul_measure, Complex.real_smul]
  have hsub : Function.mulSupport (fun v => ((c v).toReal : ℂ)) ⊆ (T : Set (Pl (F := F))) := fun v hv => by
    by_contra h
    exact hv (by show ((c v).toReal : ℂ) = 1; rw [hc1 v (hT v h)]; simp)
  have hs2 : (Function.mulSupport fun v => ∫ z, φ v z ∂(μv v)).Finite :=
    (Filter.eventually_cofinite.1 hev).subset fun v hv h => hv (by
      show ∫ z, φ v z ∂(μv v) = 1
      rw [h]; exact hind1 v)
  have hCprod : ∏ᶠ v, ((c v).toReal : ℂ) = (Cr : ℂ) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, hCrdef, Complex.ofReal_prod]
  rw [integral_smul_measure, hE, ENNReal.toReal_ofReal (div_nonneg hCr htpos.le), hc₀eq, finprod_congr hloc,
    finprod_mul_distrib (T.finite_toSet.subset hsub) hs2, hCprod, Complex.real_smul]
  have ht0' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0
  rw [Complex.ofReal_div]
  field_simp

end GlobalTheory.WeylMeas

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormula =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflection =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflection", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.LocInv

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance borelFvLoc (v : Pl (F := F)) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitWeil

end GlobalTheory.WeylFour.LocInv

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflection =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductChar =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductChar", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylTwist

open GlobalTheory.SympChange GlobalTheory.HeisSchA

theorem pure_mul_psi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ (κ : Type) [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (y : κ → AF F),
    (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
    (∀ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) ∈ SB (κ → Fv F v)) ∧
    (∀ᶠ v in cofinite, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) = GlobalTheory.SympChange.indO v) ∧
    ∀ x, pure f φ x * ψ (x ⬝ᵥ y) = (f (fun i => evI F (x i)) * eInf (fun i => evI F (x i)) (fun i => evI F (y i))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) *
        GlobalTheory.LatVac.psiAt ψ v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i))) := by
  intro F _ _ ψ hψ hunr κ _ f φ y hφ hφO
  have hlc := GlobalTheory.SympUnip.psiAt_isLocallyConstant ψ hψ.1
  have hyint : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F :=
    eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (y i)
  refine ⟨fun v => ⟨(hφ v).1.mul ((hlc v).comp_continuous (continuous_id.dotProduct continuous_const)),
    (hφ v).2.mul_right⟩, ?_, fun x => ?_⟩
  · filter_upwards [hunr, hφO, hyint] with v hv hφv hy
    funext z
    rw [hφv]
    by_cases hz : z ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · have hm : (z ⬝ᵥ fun i => evFin F v (y i)) ∈ v.adicCompletionIntegers F :=
        sum_mem fun i _ => mul_mem (hz i) (hy i)
      have h4 := (hv 1).2 (one_mem _) _ hm
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, mul_one]
    · rw [indO, Set.indicator_of_notMem hz, zero_mul]
  · have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφO, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl (F := F), evalV F v (p2 (x ⬝ᵥ y)) =
        (fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i) := fun v =>
      RingHom.map_dotProduct (evFin F v : AF F →+* Fv F v) x y
    obtain ⟨hs, hp⟩ := GlobalTheory.SympUnip.finChar_eq_finprod ψ hψ.1 (p2 (x ⬝ᵥ y))
    simp only [hq] at hs hp
    let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    have h3 : ψ (mk (p1 (x ⬝ᵥ y)) 0) = eInf (fun i => evI F (x i)) (fun i => evI F (y i)) := by
      have e1 : evI F (mk (p1 (x ⬝ᵥ y)) 0) = (fun i => evI F (x i)) ⬝ᵥ fun i => evI F (y i) :=
        RingHom.map_dotProduct q x y
      rw [hψ.2.2 _ (at_mk _), e1, eInf]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [finprod_mul_distrib hfin hs, ← hp, map_eq_mul ψ (x ⬝ᵥ y), h3]
    ring

end GlobalTheory.WeylTwist

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductChar =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOpBOfMemClosure\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare\nimport Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeBij

open GlobalTheory.SympChange GlobalTheory.LeviOp GlobalTheory.SympUnip GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Levi

variable {F : Type} [Field F] [NumberField F] {κ : Type}


open scoped Classical in
theorem levi_mapsTo [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F) (hA : IsUnit A.det) :
    ∀ Φ ∈ schA F κ, LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) Φ ∈ schA F κ := by
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
        pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
    intro f g
    funext x
    simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · congr 1
      funext i
      exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
  have hle : schA F κ ≤ (schA F κ).comap
      (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show _ ∈ schA F κ
    rw [key]
    exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
  exact fun Φ hΦ => hle hΦ


end Levi


end GlobalTheory.SympChangeBij


end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel =====
