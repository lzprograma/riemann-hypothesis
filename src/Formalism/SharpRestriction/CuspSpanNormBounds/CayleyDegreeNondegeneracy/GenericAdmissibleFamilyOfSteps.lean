module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.SharpRestriction.ParConsts
import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleAllConstants, Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps

-- ===== clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleAllConstants =====
-- clump-header: {"m": "Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleAllConstants", "h": "module\n\npublic import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow\npublic import Mathlib.NumberTheory.NumberField.ClassNumber\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality\npublic import Formalism.LocalRingCardinality.DataParams₂\nimport Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro\nimport Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners\nimport Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub\npublic import Formalism.SharpRestriction.ParConsts\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

section SW

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def classWeightAlt : ℝ :=
  (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f

end SW

section W0

variable (D : D7) (large₂ : SizeData₂ D)

end W0

section SWF

variable {eps : ℝ} (Fm : FamP eps)

end SWF

end Formalism.MainNotions.BridgeLemma₂

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleAllConstants =====

-- ===== clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps =====
-- clump-header: {"m": "Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps", "h": "module\n\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleAllConstants\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality\nimport Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

section Eqv

variable (D : D7)

end Eqv

section Sat

variable (D : D7)

end Sat

section Sub

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def PrimitiveMeanCorankOne (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ de : ℕ, 1 ≤ de → ∀ HH : ℝ, (de : ℝ) ≤ HH → NT D u ≤ HH →
    MeanLe D F0 what₂ (fun Λ => cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - 1) de)
      (((de : ℝ) / NT D u) ^ (D.R.k - 1) * (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))

end Sub

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps =====
