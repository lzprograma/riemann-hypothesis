module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Basic.Finite.Defs
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowDivZero
public import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

instance : Infinite Kf := Infinite.of_injective (Nat.cast : ℕ → Kf) Nat.cast_injective

end Formalism.BasicNotions.Examples₂.NZ
