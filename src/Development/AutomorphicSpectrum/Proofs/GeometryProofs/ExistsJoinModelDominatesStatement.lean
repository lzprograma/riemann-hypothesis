module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.InChartOfMemCtrSet
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFraction
import Mathlib.Tactic.NormNum.LegendreSymbol
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinExists

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominatesStatement

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominatesStatement =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominatesStatement", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFraction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinExists\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.exists_join_model_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i :=
  @_root_.PositivityTheory.HtPt.Mb.join_exists
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominatesStatement =====
