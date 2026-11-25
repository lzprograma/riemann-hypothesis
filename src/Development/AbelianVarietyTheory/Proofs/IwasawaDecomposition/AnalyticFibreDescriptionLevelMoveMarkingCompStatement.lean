module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingComp
public import Formalism.LocalRingCardinality.DataHost
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
open GlobalTheory.OneMapRef GlobalTheory.WeilParts


theorem _root_.GlobalTheory.T.analyticFibre_description_levelMove_marking_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (gM : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c ℂ), levR (gM, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La)) y y' → ∀ A : AnFib X bas idx e x L y, ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  first | exact @GlobalTheory.Dict.FibreMove.anFib_levR_id
