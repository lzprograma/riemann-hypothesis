module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem hasIwasawa_KAd_selfDual : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (KAd D.sp.cm.sig (dblSp A).gram L a) := by
  intro D A L a hL ha
  have : Submodule.IsFullLattice D.host.E L := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  refine HasIwasawa.adelic (fun v => ?_) (fun w => GlobalTheory.T.iwasawa_doubled_hermitian_space_real_place D A a ha w)
  by_cases hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
  · exact _root_.GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split D A L hL v hv
  · exact _root_.GlobalTheory.InertIwasawa.hasIwasawa_inert D A L hL v hv

theorem hasIwasawa_Khat (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)) (ha : IsMaj A a) :
    HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
  hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) ha

end GlobalTheory.Core.Rk.IP
