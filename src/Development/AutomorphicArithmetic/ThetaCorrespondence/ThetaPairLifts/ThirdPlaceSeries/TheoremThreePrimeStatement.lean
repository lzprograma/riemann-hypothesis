module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

@[expose] public section



section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
def Adm3PVariant (D : D7) : Prop := SumRepresentations.tieLab D ∧ _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
def ThreePrimeTheoremStatement (D : D7) : Prop := _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D → TheoremThreePrime D
end Formalism.MainNotions.AdmissibleThreePrime
end
end
