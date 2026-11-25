module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHens
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfTop
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.UnitarySelfGeneration

theorem bt_sub_eq_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  _root_.PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

theorem bt_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  _root_.PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

end PositivityTheory.UnitarySelfGeneration
