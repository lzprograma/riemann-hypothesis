module

import Development.EtaleCohomology.TateTwists.acycIffPf
public import Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocallyLifts
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_sheaf_short_complex_exact_iff_local_lifts_holds : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts := by
  intro R _ S
  exact LateralTheory.EtaleFoundations.acycIffPf.exact_iff S
