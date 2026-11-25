module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Tactic.NormNum.LegendreSymbol
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr, Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr

-- ===== clump member: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Noetherian\npublic import Mathlib.RingTheory.DiscreteValuationRing.Basic\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\npublic import Mathlib.RingTheory.KrullDimension.Field\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt\npublic import Mathlib.RingTheory.DedekindDomain.Basic\npublic import Mathlib.RingTheory.DiscreteValuationRing.TFAE\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem normal_scheme_height_one_stalk_dvr : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) := by
  intro X _ hn p hd
  obtain ⟨h1, h2⟩ := hn p
  refine ⟨h1, ?_⟩
  have hnf : ¬ IsField (X.presheaf.stalk p) := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hd
    exact zero_ne_one hd
  have hk : Ring.KrullDimLE 1 (X.presheaf.stalk p) := Ring.krullDimLE_iff.2 (by rw [hd]; rfl)
  have hd1 : Ring.DimensionLEOne (X.presheaf.stalk p) :=
    ⟨fun hne hp => Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk _ hne hp⟩
  have hdd : IsDedekindDomain (X.presheaf.stalk p) := {}
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk p) hnf).out 3 1).1 hdd

end PositivityTheory.UnitarySelfGeneration
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Noetherian\npublic import Mathlib.RingTheory.DiscreteValuationRing.Basic\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\npublic import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem stalk_isDiscreteValuationRing_of_dim_one : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) :=
  @PositivityTheory.UnitarySelfGeneration.normal_scheme_height_one_stalk_dvr

end GlobalTheory.CompanionTheory.Ar
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr =====
