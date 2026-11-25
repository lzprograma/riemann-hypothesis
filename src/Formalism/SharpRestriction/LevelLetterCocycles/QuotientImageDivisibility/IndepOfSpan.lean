module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExistsInfFilVEqBot
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.MC

open Module Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

export Formalism.MainNotions.N.Ln34.CrystallineExponents (sumAt sumAt_apply Ub mem_Ub Ub_anti count_step indep_of_span)

section Cnt

variable {LL : Type} [Field LL] {E : Type} [AddCommGroup E] [Module LL E]
variable {r : ℕ} {Fil : ℤ → Submodule LL E} (hFa : Antitone Fil) (D : Submodule LL E)
  [FiniteDimensional LL D] {e : Fin r → ℤ → E}

include hFa in
theorem smulS_sub_cc {M : ℤ} {f : ℤ → E} (hf : LB M f) (hfF : ∀ k, f k ∈ Fil (-k))
    (g : PowerSeries LL) (j : ℤ) :
    smulS g f j - PowerSeries.constantCoeff g • f j ∈ Fil (-j + 1) :=
  Formalism.MainNotions.N.Ln34.CrystallineExponents.smulS_sub_cc hFa hf hfF g j

include hFa in
theorem dvd_of_dg (a₁ : ℤ) (h₁ : D ⊓ Fil a₁ = ⊥) (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hind : ∀ c : Fin r → LL, (∀ j, ∑ m, c m • e m j ∈ Fil (-j + 1)) → c = 0) :
    ∀ (k : ℕ) (g : Fin r → PowerSeries LL),
      (∀ j : ℤ, ∑ m, smulS (g m) (e m) j ∈ Fil ((k : ℤ) - j)) → ∀ m, PowerSeries.X ^ k ∣ g m :=
  Formalism.MainNotions.N.Ln34.CrystallineExponents.dvd_of_dg hFa D a₁ h₁ he hind

end Cnt

end Formalism.MainNotions.N.Pv.LocalLengthBound.MC
