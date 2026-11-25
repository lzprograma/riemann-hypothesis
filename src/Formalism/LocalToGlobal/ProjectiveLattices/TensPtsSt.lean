module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X : Scheme.{0}} (A : Over X)

def powO : ℕ → Over X
  | 0 => 𝟙_ (Over X)
  | k + 1 => A ⊗ powO k

def tup {T : Over X} : (k : ℕ) → (Fin k → (T ⟶ A)) → (T ⟶ powO A k)
  | 0, _ => toUnit T
  | k + 1, a => lift (a 0) (tup k fun j => a j.succ)

variable [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O] (act : OAct O A)


end Formalism.L2.Pj
