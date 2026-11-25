module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin
import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.DualLattices.PowMemCarrier

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Rc ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
open scoped Matrix
