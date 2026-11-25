module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormula

@[expose] public section

namespace PositivityTheory.PfSWUS.HMass

theorem oneVecBinaryMass : OneVecBinaryMass := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM2 d b
  subst hM2
  exact ⟨1, GlobalTheory.CompanionTheory.SW.UnitVal.density_unit_lattice F E σ hCM 2 J hJ (by decide) d b⟩

theorem siegelDensitiesLowA_of_leaves (hE1 : OneVecBinary) (hB : SchwartzDensInf) : SiegelDensitiesLowA :=
  siegelDensitiesLowA_of hE1 oneVecBinaryMass hB

end PositivityTheory.PfSWUS.HMass
