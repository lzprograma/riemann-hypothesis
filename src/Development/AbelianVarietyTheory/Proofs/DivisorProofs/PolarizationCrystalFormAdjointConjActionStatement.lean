module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

theorem _root_.GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm K (HdR A)}, IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  first | exact @GlobalTheory.PolAdjoint.polForm_adjoint
