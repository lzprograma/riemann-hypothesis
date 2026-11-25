module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.UiwPow
public import Development.AutomorphicArithmetic.TwistedTraces.IwahoriCompactOpenAndIwCosetIndicatorTest
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.UnitTrace
import Development.AutomorphicArithmetic.TwistedTraces.ArchimedeanBaseChangeTraceComparison
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEDefs, Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul, Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FdFixed

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEDefs =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEDefs", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.L1
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

def TermE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ, Module.finrank F E = k + 1 → 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (m : ∀ u : Pl E, Measure (Gw n u)),
      (∀ u, (m u).IsHaarMeasure) →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v, RankOne μ V u.1 (T.J u.1) (T.χ u.1)) →
    ∀ (τ₀ : SmIrr (Gw n w₀.1)) (τ : ∀ v : Pl F, SmIrr (Gw n (T.mk' v).1)), Occurs μ V w₀.1 τ₀ →
      (∀ v ∈ T.sp, Occurs μ V (T.mk' v).1 (τ v)) → ∀ y : ℝ, 0 < y →
      ∃ c : ℂ, (T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ → c ≠ 0) ∧
        ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
        ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 →
        ∀ (j : ℕ) (sq : ℂ) (t : Pl F → ℂ), HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • e)).indicator 1) sq →
          (∀ v ∈ T.sp, HasTrace (m (T.mk' v).1) (τ v).ρ (ψ v) (t v)) →
          trOn (eigIn V 𝔢.toAmp.A (y ^ (k + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) = c * sq * ∏ v ∈ T.sp, t v

end UpperTheory.ConvolutionTheory.C
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEDefs =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEDefs\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.UiwPow\npublic import Development.AutomorphicArithmetic.TwistedTraces.IwahoriCompactOpenAndIwCosetIndicatorTest\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.C.termE :
    UpperTheory.ConvolutionTheory.C.TermE := by
  classical
  intro F E _ _ _ _ _ _ σ hgen k n hk hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF harch _ _ m hm q w₀ hq T V hV hVθ
    hrank τ₀ τ hocc₀ hocc y hy
  obtain ⟨c₁, hc₁, hside⟩ := UpperTheory.ConvolutionTheory.L1.sideTrace F E σ hgen k n hk hn μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq
    T V hV hVθ hrank y hy
  obtain ⟨r, p, hpinj, hpr⟩ : ∃ (r : ℕ) (p : Fin r → Pl F), Function.Injective p ∧ ∀ v, v ∈ T.sp ↔ v ∈ Set.range p := by
    refine ⟨T.sp.card, fun i => (T.sp.equivFin.symm i).1, ?_, fun v => ⟨fun hv => ⟨T.sp.equivFin ⟨v, hv⟩, by simp⟩, ?_⟩⟩
    · exact Subtype.val_injective.comp T.sp.equivFin.symm.injective
    · rintro ⟨i, rfl⟩
      exact (T.sp.equivFin.symm i).2
  have hpm : ∀ i, p i ∈ T.sp := fun i => (hpr _).2 ⟨i, rfl⟩
  let mm : ∀ u : Pl E, Measure (Gw n u) := fun u => (m u (T.J u))⁻¹ • m u
  have h0 : ∀ u, m u (T.J u) ≠ 0 := fun u => by
    haveI := hm u
    exact ((T.co u).2.measure_pos (m u) ⟨1, Subgroup.one_mem _⟩).ne'
  have ht0 : ∀ u, m u (T.J u) ≠ ⊤ := fun u => by
    haveI := hm u
    exact (T.co u).1.measure_lt_top.ne
  have hmm : ∀ u, (mm u).IsHaarMeasure := fun u => by
    haveI := hm u
    exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (ht0 u)) (ENNReal.inv_ne_top.2 (h0 u))
  have hmm1 : ∀ u, mm u (T.J u) = 1 := fun u => by
    simp only [mm, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (h0 u) (ht0 u)]
  obtain ⟨c₂, hc₂, htr⟩ := UpperTheory.archimedean_baseChange_trace_comparison F E σ k n hn μ D s hs hposition νF a m hm q w₀ hq
    T V hV τ₀ τ hocc₀ hocc y hy mm (fun _ => rfl) r p hpinj hpr
  refine ⟨c₁ * c₂, fun hZ => mul_ne_zero hc₁ (hc₂ hZ), fun L ψ hfit e l 𝔢 he hsd j sq t hsq ht => ?_⟩
  have hB : ∀ i, ∃ B, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) B := fun i => by
    haveI := hmm (T.mk' (p i)).1
    exact (UpperTheory.ConvolutionTheory.C.olocEx E n μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (hfit.test _ (hpm i)).1).exists
  choose B hB using hB
  rw [hside L ψ hfit e l 𝔢 hsd r p hpinj hpr (fun i => mm (T.mk' (p i)).1) (fun i => ⟨hmm _, hmm1 _⟩) B hB j,
    htr ψ (fun v hv => ⟨(hfit.test v hv).1, fun u hu g => ((hfit.test v hv).2 u hu g).1⟩) e he j sq t hsq ht B hB]
  ring
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FdFixed =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FdFixed", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.UnitTrace
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem fd_fixed {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    (m : Measure G) (ρ : Representation ℂ G V) (J : Subgroup G) (hJ : MeasurableSet (J : Set G))
    (h1 : m (J : Set G) = 1) (A : V →ₗ[ℂ] V) (hA : IsIntegralOp m ρ ((J : Set G).indicator 1) A)
    (hf : FiniteDimensional ℂ (LinearMap.range A)) : FiniteDimensional ℂ (fixedVectors ρ J) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A) fun x hx => ?_
  have hAx : A x = x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA x l).2, sub_eq_zero]
    have e : (fun g => ((J : Set G).indicator (1 : G → ℂ)) g * l (ρ g x)) =
        (J : Set G).indicator fun _ => l x := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · have hgx : ρ g x = x := hx g hg
        simp [Set.indicator_of_mem hg, hgx]
      · simp [Set.indicator_of_notMem hg]
    rw [e, integral_indicator hJ]
    simp [Measure.real, h1]
  exact ⟨x, hAx⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.ConvolutionTheory.T.termE :
    UpperTheory.ConvolutionTheory.T.TermE := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn m hm μ _ θ hθ D s hs hsl νE _ νF _ b a aE aF hAS q w₀ hq T V hV hVθ hR hne _ _ mm hmm
    τ hocc ν hν
  obtain ⟨y, hy, hY⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS q w₀ hq T V hV hVθ hR).1 hne
  have hJ : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
  have hcoI : CO (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := hJ ▸ T.co w₀.1
  haveI := hmm w₀.1
  have h0 : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ 0 :=
    hcoI.2.measure_ne_zero _ ⟨1, one_mem _⟩
  have hT : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ ⊤ :=
    hcoI.1.measure_lt_top.ne
  obtain ⟨m₀, hm₀, hm₀1⟩ : ∃ m₀ : Measure (Gw n w₀.1), m₀.IsHaarMeasure ∧
      m₀ (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) = 1 := by
    refine ⟨(mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)))⁻¹ • mm w₀.1,
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT) (ENNReal.inv_ne_top.2 h0), ?_⟩
    simp [ENNReal.inv_mul_cancel h0 hT]
  haveI := hm₀
  have hmm' : ∀ u, (Function.update mm w₀.1 m₀ u).IsHaarMeasure := by
    intro u
    by_cases h : u = w₀.1
    · subst h
      simpa using hm₀
    · simpa [Function.update_of_ne h] using hmm u
  obtain ⟨c, hc, hmain⟩ := UpperTheory.ConvolutionTheory.C.termE F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS
    (Function.update mm w₀.1 m₀) hmm' q w₀ hq T V hV hVθ hR (τ w₀.1) (fun v => τ (T.mk' v).1) (hocc _) (fun v _ => hocc _) y hy
  have hYZ : T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≤ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y := by
    unfold Ty.Y Ty.Z Ty.typed
    exact inf_le_inf_left _ (le_iInf₂ fun w _ => iInf_le _ w)
  have hZne : T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ := fun h => hY (le_bot_iff.1 (h ▸ hYZ))
  have hfix : V ⊓ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) ≠ ⊥ := by
    intro h
    refine hY (le_bot_iff.1 (h ▸ le_inf ?_ ?_))
    · exact inf_le_left.trans inf_le_left
    · have heig := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w₀.1 (T.J w₀.1) (T.χ w₀.1) (T.co _) (T.chr _)).2.1
      have hχ : T.χ w₀.1 = 1 := T.triv q hq w₀
      rw [← hJ, ← heig, ← hχ]
      exact inf_le_right.trans (iInf_le _ w₀.1)
  obtain ⟨hfx, -, -, s₀, -, A, hA, hfin, -⟩ :=
    UpperTheory.ConvolutionTheory.T.unitTrace E n μ V hV w₀.1 m₀ hm₀ (τ w₀.1) _ (hocc _) hcoI hfix
  have fd := fd_fixed m₀ (τ w₀.1).ρ _ hcoI.2.measurableSet hm₀1 A hA hfin
  obtain ⟨Z, hZ0, hcard, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow E n w₀.1 m₀ hm₀1 (τ w₀.1) ν hν fd
  refine ⟨y ^ (m + 1), c, Z, pow_pos hy _, hc hZne, ?_, hZ0, ?_⟩
  · rintro rfl
    exact hfx (Submodule.finrank_eq_zero.1 (by simpa using hcard.symm))
  · intro L ψ hF l 𝔢 hS sv hsv j
    refine hmain L ψ hF ν l 𝔢 hν hS j _ sv ?_ ?_
    · rw [Function.update_self]
      exact hZ j
    · intro v hv
      have hne' : (T.mk' v).1 ≠ w₀.1 := by
        intro h
        have hvq : v = q := by rw [← under_eq (T.mk' v), h, under_eq w₀]
        exact T.q_not (hvq ▸ (Finset.mem_filter.1 hv).1)
      rw [Function.update_of_ne hne']
      exact hsv v hv
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FdFixed =====
