module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Units
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.NumberTheory.NumberField.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum

namespace UpperTheory.V.B3

def pPart (m p : ℕ) : Subgroup (ZMod m)ˣ := (ZMod.unitsMap (Nat.ordCompl_dvd m p)).ker

end UpperTheory.V.B3

end
