module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

theorem _root_.GlobalTheory.T.inGeo_half_of_ratHyp0 : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p → ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m), RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j → InGeo (geoHalf p) := by
  first | exact @_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0
end
