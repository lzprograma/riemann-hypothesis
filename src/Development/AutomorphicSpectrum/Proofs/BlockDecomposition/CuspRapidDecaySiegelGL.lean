module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.CuspFinGL

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (_root_.GlobalTheory.CompanionTheory.GGPS.smooth_automorphic_open_invariant E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (_root_.GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

end GlobalTheory.CompanionTheory.CuspFinGL
