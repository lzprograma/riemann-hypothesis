module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison

def ModelComponents : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  CompM (Model.Sm (l := l) (K := K)) ∧ CompM (Model.Good (l := l) (K := K))

def GeometricGenericComponents : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K), M.Good →
  ∀ d, M.Conn d → M.Geo

structure FormalIn : Prop where
  a6ring : GlobalTheory.EtC.DivisorRingCompatibility
  a9 : GlobalTheory.EtC.A9
  et : E.EtIn

def RootsOfUnityFormal : Prop := FormalIn → InRoot

def SumInputFromFormal : Prop := FormalIn → InSum

end CrystallineSemistableComparison
