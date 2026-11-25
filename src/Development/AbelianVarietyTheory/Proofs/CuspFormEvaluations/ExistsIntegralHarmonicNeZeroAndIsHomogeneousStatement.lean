module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneous
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (Dom a n → Dw.p + Dw.q ≤ n → ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P.IsHomogeneous (Formalism.L2.Pj.DF Dw a) := by
  first | exact @GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous
