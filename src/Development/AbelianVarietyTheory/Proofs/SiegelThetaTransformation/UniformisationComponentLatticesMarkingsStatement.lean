module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.uniformisation_component_lattices_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp), (U.X k).κ0 = 2 * (U.X k).ξ0 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ r = (W.F.Di (W.ik k)).p + (W.F.Di (W.ik k)).q ∧ Function.Injective (W.emb k) ∧ Submodule.span E (Set.range (W.emb k)) = ⊤ ∧ ∀ a b, (((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (W.emb k a) (W.emb k b) := by
  first | exact @GlobalTheory.Dict.uw_lattice
