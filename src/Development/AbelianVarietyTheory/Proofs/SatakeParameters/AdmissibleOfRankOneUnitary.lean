module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem admissible_of_rank_one_unitary : ∀ (D : D7) (T : WDTie D.nd D.naut), RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → Formalism.MainNotions.SumRepresentations.adm7 D := by
  intro D T hT h2
  exact (_root_.GlobalTheory.RowTie.tempered_all_ranks D T hT h2).1

end GlobalTheory.RowTie
