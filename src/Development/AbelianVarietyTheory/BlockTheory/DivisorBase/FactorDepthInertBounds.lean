module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def boundAll (p i k : ℕ) : ℝ := (i : ℝ) * k / ((p : ℝ) - 1)

def boundInert (p j' i k : ℕ) : ℝ := 2 * (i : ℝ) * k / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * (j' : ℝ) * k / ((p : ℝ) - 1)

def boundFine (p N j' i k : ℕ) : ℝ :=
  (k : ℝ) * ((N : ℝ) - 2 * j' - i) * p / ((p : ℝ) ^ 2 - 1) +
    (k : ℝ) * j' * (3 + 1 / 2 * Real.logb p k) / ((p : ℝ) - 1) + (i : ℝ) ^ 2 * (Real.logb p k + 1)

variable {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
  {p : ℕ} [Fact p.Prime]

end GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds
