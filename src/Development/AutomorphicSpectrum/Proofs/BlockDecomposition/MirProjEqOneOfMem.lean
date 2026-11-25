module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mem_of_mirProj_eq_one' <;> assumption

end Alg

end GlobalTheory.CompanionTheory.BZMirAdj
