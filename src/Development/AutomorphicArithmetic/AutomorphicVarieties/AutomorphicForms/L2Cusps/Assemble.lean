module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
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

@[expose] public section

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_split (h : SplitEq) (s : {r : ℝ // 0 < r}) :
    ∃ t : ℝ, Reduction.centralSection E a s = splitCentre E a t := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Subsingleton.elim _ _⟩
  · have h0 : ((a : ℝ) * Module.finrank ℚ E) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
    refine ⟨Real.log s.1 / (a * Module.finrank ℚ E), ?_⟩
    rw [h]
    congr 1
    refine Subtype.ext ?_
    change s.1 = Real.exp _
    rw [mul_div_cancel₀ _ h0, Real.exp_log s.2]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem retractOne_surjective : Function.Surjective (retractOne : GA E a → G1 E a) :=
  fun x => ⟨x, retractOne_coe x⟩

theorem range_cmp (h1 : RangeLe) (h2 : ContMem) {μ : Measure (GA E a)} [μ.IsHaarMeasure]
    {μ₁ : Measure (G1 E a)} [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) :
    LinearMap.range (cmp hp).toLinearMap = L2cusp μ := by
  refine le_antisymm ?_ (L2cusp_le ?_ fun φ hφ h => h2 E a μ μ₁ hp φ hφ h)
  · rintro _ ⟨v, rfl⟩
    exact h1 E a μ μ₁ hp v
  · exact (cmp hp).isometry.isClosedEmbedding.isClosed_range

theorem partA (hH : MuHaar) (hP : QuotPres) (hE : CmpEquiv) (h1 : RangeLe) (h2 : ContMem) (hC : AbsCompact) :
    GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  intro E _ _ _ a μ _ _
  have := hH E a μ
  have hp := hP E a μ
  exact EnoughCompact.isDiscreteSum (isUnitaryRep_Rcusp μ)
    (hC _ _ _ _ (cuspRepT (muOne μ)) (muOne μ) _ _ (isSubrep_L2cusp μ) (cmp hp) retractOne retractOne_surjective
      (hE E a μ _ hp) (range_cmp h1 h2 hp) fun f => isCompactOperator_cuspRep (muOne μ) f)

theorem partC (hS : SplitEq) (hB : BrCusp) : GlobalTheory.Published.CuspFormsBoundedGL := by
  intro E _ _ _ a φ hφ hn
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms (hB E a φ hφ)
  refine ⟨C, fun g => ?_⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL g
  obtain ⟨t, ht⟩ := exists_split (E := E) (a := a) hS s
  rw [ht, hn]
  exact hC y hy

end UpperTheory.V.KernelIndexFullLattice
