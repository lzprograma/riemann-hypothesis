module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlCGTruegalEx

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
theorem galEx_of_cgTrue_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL →
    _root_.UpperTheory.GalS.CuspUAlt → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
      Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T) → GalEx D :=
  fun hL hF hG _ _ ⟨C⟩ => C.galEx hL hF hG
end GlobalTheory.HeightCounting
end
end
