module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH

@[expose] public section



section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
variable {T : WDTie N A} (S : Reading T)
def LawsAlt : Prop :=
  ∀ (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), _root_.UpperTheory.One.M.RecLawsH (S i w hw).rc
end GlobalTheory.SplitRead
end
end
