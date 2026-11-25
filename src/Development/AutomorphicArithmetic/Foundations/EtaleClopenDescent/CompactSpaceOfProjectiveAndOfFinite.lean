module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct

@[expose] public section

open AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem UpperTheory.Cb.compactSpace_projective_space (N : ℕ) : CompactSpace (PSpace ℂ N) :=
  QuasiCompact.compactSpace_of_compactSpace
    (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase ℂ N)

theorem UpperTheory.Cb.compactSpace_of_projective_and_of_finite :
    (∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ), IsProjOver s → CompactSpace Z) ∧
      ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z), IsFinite c → CompactSpace Z → CompactSpace Y := by
  refine ⟨?_, ?_⟩
  · rintro Z s ⟨N, i, hi, -⟩
    have := UpperTheory.Cb.compactSpace_projective_space N
    exact QuasiCompact.compactSpace_of_compactSpace i
  · intro Y Z c hc hZ
    exact QuasiCompact.compactSpace_of_compactSpace c
