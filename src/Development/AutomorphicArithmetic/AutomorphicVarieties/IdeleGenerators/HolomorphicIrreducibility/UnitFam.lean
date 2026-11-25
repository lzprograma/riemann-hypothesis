module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EulerianNumeratorThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LevelOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.UnitFamC

@[expose] public section

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.unitFam :
    UpperTheory.V.Sd.UnitFam := by
  intro l _ hl ι N _ hN hlN
  obtain ⟨k₀, hk₀⟩ := UpperTheory.V.Z.Sym.Unl.unitFamC (l := l) hl ι (N := N) hN hlN
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨F, hfam, hint, hvan, hu, h0, -⟩ := hk₀ k hk
  exact ⟨F, hfam, hint, hvan, hu, h0⟩
