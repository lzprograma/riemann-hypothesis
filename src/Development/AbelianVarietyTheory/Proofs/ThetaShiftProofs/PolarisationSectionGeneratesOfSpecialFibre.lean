module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratesOfNonzeroOnSpecialFibre
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.GenDvr

open IsLocalRing ReciprocityTheory.ChartRestriction.G.H1

theorem generates_of_nonzero_on_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  intro _ h₂ E _ _ _ H Dw l Xo _ T G t' x m₁ m₂ θ ⟨g, hg, hθ⟩ σ
  have := G.semi.smooth
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre h₂.secTwist amplePt Xo.univ m₁
  obtain ⟨w, hw, -⟩ := m₂.lin
  exact GlobalTheory.IntegralPull.generates_of_generic_line G.G.hom m₂.cart.1 G.PP.isLB t'.PP.isLB ⟨w, hw⟩ b (fun s => (hb s).exists) θ hg hθ σ

end GlobalTheory.GenDvr
