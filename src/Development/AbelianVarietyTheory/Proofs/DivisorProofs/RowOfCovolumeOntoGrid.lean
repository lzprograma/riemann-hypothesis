module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.FourBoundsAtBundles

end GlobalTheory.Fc.FourBoundsAtBundles

namespace GlobalTheory.Fc.FourBoundsAtBundles

open GlobalTheory.Fc.R1

theorem evW_of_atAll {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

end GlobalTheory.Fc.FourBoundsAtBundles
