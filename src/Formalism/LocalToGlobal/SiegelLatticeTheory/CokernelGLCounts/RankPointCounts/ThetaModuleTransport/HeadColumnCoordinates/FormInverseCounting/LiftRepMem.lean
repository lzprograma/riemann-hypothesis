module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumMapCompSub

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) {r : ℕ}

theorem elim_eta (Y : Ix r → O) : Y = Sum.elim (fun j => Y (Sum.inl j)) (fun j => Y (Sum.inr j)) := by
  funext i
  cases i <;> rfl

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
