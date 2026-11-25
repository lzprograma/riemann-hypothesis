module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBound
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.GodementSumW
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDetParabolicFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIffFrameParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactFrameEquiv
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.IsGrowFormEvAt

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.IsGrowFormEvAt =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.IsGrowFormEvAt", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuation\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBound\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.GodementSumW\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDetParabolicFrame\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIffFrameParabolic\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity\npublic import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Aeis

def evAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {Y : Spc F E n} (x : G2 σ Y) : modFun σ Y →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp (modFun σ Y).subtype

end PositivityTheory.SiegelWeilFormula.Aeis

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.IsGrowFormEvAt =====
