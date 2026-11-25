module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockR
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FockRAddRight
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
public import Formalism.PolynomialDimension.MultinomialDepth.FockGaussComparisonHolds

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14

export Formalism.MainNotions.ColumnSystems.Pf.TF (fock_eq_fockR Lin_X Lin_coeff_zero Lin_chain fockR_Lin
  fockR_Lin_dual Aa_dual)

theorem multDiv_kapFl (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) {n' k : ℕ} (d : Fin n' → ℕ) :
    MultDiv O p (kapFl p k d) (k := k) d :=
  Formalism.MainNotions.ColumnSystems.Pf.TF.multDiv_kapFl O p hpO d

end Formalism.MainNotions.TestSideCounting
