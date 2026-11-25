module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v := by
  first | exact @GlobalTheory.UMin.CrdUniq.main
