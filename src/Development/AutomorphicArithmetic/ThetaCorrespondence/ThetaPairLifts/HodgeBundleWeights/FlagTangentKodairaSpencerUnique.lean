module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical
namespace GlobalTheory.FlagTan
open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
theorem kodaira_spencer_map_unique : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K]
    [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
    ∀ M M' : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M →
      GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M' → M = M' :=
  fun Pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' => IsKS.unique Pr.p5 h h'
end GlobalTheory.FlagTan
end
end

