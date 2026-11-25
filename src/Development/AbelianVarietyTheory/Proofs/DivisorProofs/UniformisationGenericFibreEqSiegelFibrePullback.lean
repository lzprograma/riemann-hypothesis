module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
open GlobalTheory.TInj

namespace GlobalTheory.TInj.GenPull

alias pull_comp_iso := _root_.GlobalTheory.ZM.lbIso_pull_comp

alias pull_pull_iso := _root_.GlobalTheory.SiegelPullComp.iso_pull_pull

alias pull_id_iso := _root_.GlobalTheory.ThetaAffineGlue.lbIso_pull_id

end GlobalTheory.TInj.GenPull
