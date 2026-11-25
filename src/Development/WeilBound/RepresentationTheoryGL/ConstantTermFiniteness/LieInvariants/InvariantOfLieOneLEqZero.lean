module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalAddOfKill
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemL2OfBoundedContinuousInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.TopEig
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace PositivityTheory.Rg.HF.GL

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  exact GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspRapidDecaySiegelGL

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem cuspFin_zero : CuspFin E 0 := GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFin_zero

theorem invariant_of_lie_oneL_eq_zero {a : ℕ} (ψ : Sm E a) (h : lie E a (oneL E a) ψ = 0) (t : ℝ) (g : GA E a) :
    ψ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = ψ.1 g := by
  exact GlobalTheory.CompanionTheory.CuspFinGL.Split.invariant_of_lie_oneL_eq_zero ψ h t g

theorem cuspFin_pos {a : ℕ} (ha : 0 < a) : CuspFin E a := by
  apply _root_.GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFin_pos <;> assumption

theorem cuspFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a := by
  exact GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFin

theorem genFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GenFin E a :=
  GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters cuspFin GlobalTheory.CompanionTheory.CTFin.ctFin

theorem automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL :=
  PositivityTheory.Affgl.TopEig.top genFin

end PositivityTheory.Rg.HF.GL
