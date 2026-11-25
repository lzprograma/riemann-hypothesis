module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjSmoothAlong
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNbarLeviChartReg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth, GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def MUcSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t : ℝ),
    M.atlas.Smooth (S.bregWeight t) → IsSmoothHerm (MUc H S B p q t)

end GroundTheory.Heights₂.Heights.NineStatements
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth\npublic import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjSmoothAlong\npublic import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth\npublic import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth\nimport GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly\nimport GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos\npublic import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace MUcSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothRepConj_smooth_of {P : Ideal (MRing ι)} {A Z : HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRepConj P A) := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact TopNPoly.smoothRep_smooth_of ha hZ hh

end MUcSmooth


open MUcSmooth in
theorem MUcSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement) : MUcSmooth.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D H M w S B p q t hsm
  obtain ⟨-, Z, hZa, hZs, hZh⟩ := NbarLeviChartReg.exists_smooth_herm_of_weight hE hP D H M
    S.ref S.ref_deg S.ref_smooth (S.bregWeight t) hsm B p q
  exact smoothRepConj_smooth_of (Z := Z) hZa hZs hZh

end GroundTheory.Heights₂.Heights.NineStatements
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth =====
