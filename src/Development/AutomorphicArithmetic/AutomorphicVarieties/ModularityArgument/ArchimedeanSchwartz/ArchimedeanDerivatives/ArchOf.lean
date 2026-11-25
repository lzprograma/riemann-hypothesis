module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich
import Formalism.DoubleCosetMeasures.Statement
public import GroundTheory.AutomorphicForms.GL2.GJStandardLBump
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical


theorem UpperTheory.V.Z.Inf.archOf :
    UpperTheory.V.Z.Inf.ArchOf := by
  intro hS hF hT hB K _ _ _ n hn ψ m hm fi hfi hne μ _
  obtain ⟨hsurj, hpe, habs, e, c, c', he, hc, hc', hΦ⟩ := hB K n μ
  obtain ⟨k, hk, hS⟩ := hS K n
  obtain ⟨κ, hκ, hF⟩ := hF K n e he
  have hcont : ContinuousOn (chart ψ.1 1) (invSet K n) := fun x hx =>
    (contDiffAt_chart ψ.2 1 hx).continuousAt.continuousWithinAt
  have hval : ∀ y, fi (archComp K n (infGL K n y)) = chart ψ.1 1 (toL y.val) := by
    intro y
    rw [hfi, hpe, chart_val, one_mul]
  have hne' : ∃ x ∈ invSet K n, chart ψ.1 1 x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨_, val_mem_invSet y, by rwa [← hval]⟩
  obtain ⟨Φ, hΦt, hdiff, s₀, hs₀⟩ := hT K n _ hcont hne'
  obtain ⟨hDt, hsh⟩ := hS ψ m hm Φ hΦt
  obtain ⟨φ, hφ, hφF⟩ := hΦ Φ hΦt
  obtain ⟨φ', hφ', hφF'⟩ := hΦ _ hDt
  refine ⟨φ, φ', k, κ, hk, hκ, ?_, ?_, ?_, ?_⟩
  · have h : archZeta μ φ fi = fun s => c * (fun s : ℂ => ∫ x, Φ x * chart ψ.1 1 x * ((UpperTheory.V.Z.Inf.nrm x : ℝ) : ℂ) ^ s)
        (s + ((n : ℂ) - 1) / 2 - n) := funext fun s => hφ fi _ hcont hval s
    rw [h]
    exact (hdiff.comp ((differentiable_id.add_const _).sub_const _)).const_mul c
  · intro h0
    have h := hφ fi _ hcont hval (s₀ + n - ((n : ℂ) - 1) / 2)
    rw [h0, show s₀ + n - ((n : ℂ) - 1) / 2 + ((n : ℂ) - 1) / 2 - n = s₀ by ring] at h
    exact mul_ne_zero hc hs₀ h.symm
  · intro s
    rw [hφ' fi _ hcont hval, hφ fi _ hcont hval, hsh 1 s]
    ring
  · intro g s
    unfold archZeta
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨y, rfl⟩ := hsurj x
    have hp : ((archAbsDet (archComp K n (infGL K n y)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (archAbsDet_pos _).ne'
    simp only [archIntegrand, archDetPow]
    rw [hφF, hφF', hF Φ hΦt, show s + 1 + ((n : ℂ) - 1) / 2 = (s + ((n : ℂ) - 1) / 2) + 1 by ring,
      Complex.cpow_add _ 1 hp, Complex.cpow_one, habs]
    ring
