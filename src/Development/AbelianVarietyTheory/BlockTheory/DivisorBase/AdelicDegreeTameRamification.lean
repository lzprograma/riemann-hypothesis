module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev quadField (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {((H.rt : 𝓞 E) : E)}

instance (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def TameAtRamified (H : Host E) : Prop :=
  ∀ (l : ℕ) (w : Ideal (𝓞 E)), l.Prime → (l : ℤ) ∣ discr E → w.IsMaximal → (l : 𝓞 E) ∈ w →
    w.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w ∧
    (l ≠ H.d → ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w) ∧
    (l = H.d → (l : 𝓞 E) ∉ w ^ 3)

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
