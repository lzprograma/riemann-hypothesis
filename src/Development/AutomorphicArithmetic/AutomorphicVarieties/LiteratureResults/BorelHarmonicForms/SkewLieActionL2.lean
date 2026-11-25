module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Mathlib.Analysis.InnerProductSpace.Calculus

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant, Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.derivative_right_translate_L2 :
    UpperTheory.V.Lit.Bor.DerivativeRightTranslateL2 := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c hψc hc hc0 hcadd hder
  have hf : Continuous fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2 :=
    (GlobalTheory.AutomorphicL2Unitary.continuous_R hψ.toL2).comp hc
  have hI := hf.integral_hasStrictDerivAt 0 0
  have hE : (fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hφ.toL2) =
      fun t => (∫ s in (0 : ℝ)..t, (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2) + hφ.toL2 := by
    funext t
    rw [← GlobalTheory.CompanionTheory.TransDeriv.R_sub_eq_integral hφ hψ hψc hc hc0 hcadd hder t]
    abel
  rw [hE]
  have h := hI.hasDerivAt.add_const hφ.toL2
  simpa [hc0] using h
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2 =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.InnerProductSpace.Calculus\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem continuous_lie_of_level {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) : Continuous (lie E a X φ).1 := by
  refine ContAut.continuous_of_isOpen_stab E a _
    (_root_.GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds (finRep E a) (lie E a X φ)
      (Filter.mem_of_superset (h.mem_nhds (by show finRep E a 1 φ = φ; simp)) fun k hk => ?_))
  have e : lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) :=
    LinearMap.congr_fun (lie_rt_fin X k) φ
  have hk' : finRep E a k φ = φ := hk
  change finRep E a k (lie E a X φ) = lie E a X φ
  rw [← e, hk']

open scoped GlobalTheory.CuspRep.CuspidalL2GL in
theorem UpperTheory.V.Lit.Bor.skew_lie_action_L2 :
    UpperTheory.V.Lit.Bor.SkewLieActionL2 := by
  intro E _ _ _ a μ _ X φ ψ hφ hψ h1 h2 h3 h4
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have g0 : infGL E a (c 0) = 1 := by rw [c0, map_one]
  have key : ∀ (θ : Sm E a), IsOpen {k | act (.fin k) θ = θ} →
      ∀ (p : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ θ.1)
        (q : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X θ).1),
      HasDerivAt (fun s => GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) p.toL2) q.toL2 0 :=
    fun θ hθ p q => UpperTheory.V.Lit.Bor.derivative_right_translate_L2 (GA E a) _ μ θ.1 _ p q (fun s => infGL E a (c s))
      (continuous_lie_of_level X θ hθ) ccont g0 (fun s t => by rw [cadd, map_mul])
      (fun g => hasDerivAt_curve θ g c X c0 cder)
  have d := (key φ hφ h1 h3).inner ℂ (key ψ hψ h2 h4)
  have hc : (fun s : ℝ => inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h1.toL2)
      (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h2.toL2)) = fun _ => inner ℂ h1.toL2 h2.toL2 :=
    funext fun s => (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s))).toLinearMap
      (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
  rw [hc] at d
  have h := d.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [g0, map_one, ContinuousLinearMap.one_apply] at h
  exact (add_comm _ _).trans h
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2 =====
