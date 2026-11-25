module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockGA
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CommStar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.EntEmpty
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.VcStHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PGrowth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

def CmbPiA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (l₁ : InfinitePlace E → DomWeight n) (l₂ : InfinitePlace E → DomWeight 0) (D : Dom E n 0) (A : Ar l₁ l₂ D)
    (u₁ : GL (Fin n) E) (u₂ : GL (Fin 0) E), IsTransl u₁ → ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (l₁ v))) →
    ∀ S : Set (Pl E), IsSection S →
    ∀ Z : Finset (Pl E), SplitIn S Z → ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
    (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) → (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, ‖c‖ = c₀ ∧
    ∀ (L : Lv n 0 Z) φ T (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (C : Cmb A.blk) (R : ℝ), L.Fix φ → TEv S T e₂ →
      Disjoint T Z → C.Ok (rt u₁ u₂ (A.fx S L T φ e₁ e₂)) R → IsTwTr D.μ π (trM C.Φ A.tw)
        (c * C.val (chi l₁) (chi l₂) * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => φ w (g, 1)) * val T e₁ e₂ B 0)

theorem cmbPiA : UpperTheory.V.Z.Mult.PiTermA → TwTrSum → CmbPiA := by
  intro hPi hSum E _ _ _ hU n hn l l₂ D A u₁ u₂ hu₁
  haveI := A.ha
  haveI := A.hb
  have hμ : D.μ.IsHaarMeasure := by
    obtain ⟨h1, -, h3, h4⟩ := D.haar
    exact { }
  obtain ⟨c₁, hc₁, hP⟩ := hPi E hU n hn l u₁ hu₁ A.μa D.μ A.ha hμ
  obtain ⟨S₀, hS₀⟩ := (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E).1
  have hvol : A.blk.vol ≠ 0 := (ffAlg E n 0 l l₂ D A S₀ hS₀).1
  have hm := real_univ_ne A.μb
  generalize hmdef : (A.μb.real Set.univ : ℂ) = m at hm
  refine ⟨c₁ * ‖A.blk.vol⁻¹‖ * ‖(m⁻¹) ^ Fintype.card (InfinitePlace E)‖,
    mul_pos (mul_pos hc₁ (norm_pos_iff.2 (inv_ne_zero hvol))) (norm_pos_iff.2 (pow_ne_zero _ (inv_ne_zero hm))), ?_⟩
  intro π hreg hdual hl S hS Z hZ B τ hB hτ
  obtain ⟨c₀, hc₀, hc⟩ := hP π hreg hdual hl S hS Z hZ B τ hB hτ
  refine ⟨c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E), by rw [norm_mul, norm_mul, hc₀], ?_⟩
  exact cmbPi_core hSum E n l l₂ D A u₁ u₂ π S Z hZ B τ c₀ m hm hmdef hc

end UpperTheory.Zero.ConvolutionTheory.EB
