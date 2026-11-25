module

public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.ComplF
public import Formalism.LocalToGlobal.Columns.Inputs

@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

def GenusToPoint : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N →
    Formalism.HermitianLatticesTheory.SameGenus (hStd E n) (stdLat E n) N → ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

def LocToAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), UnimodGenusLoc E n → UnimodGenus hc n

end Formalism.L2.GenusGluing.Gen
