module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOpBOfMemClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointsIndicatorFourierSelfUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmForm
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceMemSpanPureTensors, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstant, Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceMemSpanPureTensors =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceMemSpanPureTensors", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchASpan

theorem mem_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    Φ ∈ Submodule.span ℂ {Ψ : (κ → AF F) → ℂ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
      GlobalTheory.RatWeilOp.IsFam φ ∧ Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} := by
  intro F _ _ κ _ Φ hΦ
  refine (Submodule.span_le.2 ?_) hΦ
  rintro _ ⟨f, g, hg, rfl⟩
  let L : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun g => pureA F f g
      map_add' := fun a b => by funext x; simp only [pureA, Pi.add_apply, mul_add]
      map_smul' := fun c a => by
        funext x; simp only [pureA, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have h : L g ∈ Submodule.map L (Submodule.span ℂ _) :=
    Submodule.mem_map_of_mem (GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg)
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, ⟨φ, hφ1, hφ2, rfl⟩, rfl⟩
  exact ⟨f, φ, ⟨hφ1, hφ2⟩, rfl⟩

end GlobalTheory.SchASpan

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceMemSpanPureTensors =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstant =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstant", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.FourierLocInv

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem inversion_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → k), ∀ a : κ → k,
      ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ = d * φ (-a) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨((r : ℝ) : ℂ) ^ 2, pow_ne_zero 2 hr', fun φ hφ a => ?_⟩
  have hg : (fun x => φ (x + -a)) ∈ SB (κ → k) :=
    ⟨hφ.1.comp_continuous (Homeomorph.addRight (-a)).continuous, hφ.2.comp_homeomorph (Homeomorph.addRight (-a))⟩
  have key := (GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν _ hg).2
  have hinner : ∀ y, ∫ x, φ (x + -a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m
      = (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) := by
    intro y
    rw [GlobalTheory.FourierLocBij.translate_fourier, neg_dotProduct, neg_neg, dotProduct_comm a y, mul_comm]
  have key' : ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) ∂m = φ (-a) := by
    refine Eq.trans ?_ (key.trans (congrArg φ (zero_add (-a))))
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (hinner y).symm
  have hsm : ∀ G : (κ → k) → ℂ, ∫ y, G y ∂μ = ((r : ℝ) : ℂ) * ∫ y, G y ∂m := by
    intro G
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hfun : (fun y => (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ)) =
      fun y => ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) := by
    funext y
    rw [hsm, mul_assoc]
  rw [show (∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ) =
      ∫ y, ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) ∂μ from congrArg _ hfun,
    integral_const_mul, hsm, key']
  ring

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourier_inversion : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (χ : AddChar (Fv F v) ℂ), Continuous χ → (∀ t, ‖χ t‖ = 1) →
    χ ≠ 1 → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure], ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → Fv F v), ∀ a : κ → Fv F v,
      ∫ y, (∫ x, φ x * χ (x ⬝ᵥ y) ∂μ) * χ (y ⬝ᵥ a) ∂μ = d * φ (-a) := by
  intro F _ _ v χ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (GlobalTheory.FourierLocBij.toCircle χ hn) := Continuous.subtype_mk hc _
  have hne : GlobalTheory.FourierLocBij.toCircle χ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [GlobalTheory.FourierLocBij.coe_toCircle] using
      congrArg (fun ψ : AddChar (Fv F v) Circle => ((ψ t : Circle) : ℂ)) h
  exact inversion_circle (GlobalTheory.FourierLocBij.toCircle χ hn) hcont hne κ μ

end GlobalTheory.FourierLocInv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstant =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOpBOfMemClosure\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceMemSpanPureTensors\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointsIndicatorFourierSelfUnramified\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstant\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylBij

open GlobalTheory.WeylFourier GlobalTheory.RatWeilOp


end GlobalTheory.WeylBij

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective =====
