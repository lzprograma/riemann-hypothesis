module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaArc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU GlobalTheory.LN

namespace GlobalTheory.ThetaClosed

theorem nonzeroLocus_firstPower_section_subset {X : Scheme.{0}} {L : LB X} (σ : H0 L 1) {x : X} (hx : x ∈ nonzeroLocus σ) :
    x ∈ nonzeroLocus (DVR.secOfH0 σ) := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j 0, funext fun a => congrArg j (Subsingleton.elim a 0)⟩
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have e := X.basicOpen_res (σ.f fun _ => i) (homOfLE (DVR.chart_le_weighted_chart_single (L := L) i)).op
  exact e.ge ⟨DVR.h0_le (fun _ => i) (X.basicOpen_le _ hj), hj⟩

theorem exists_section_nonzero_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → CharZero R → ∀ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal R) D A G), ∃ θ : LB.Sec U.LG.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R := by
  intro R _ _ _ hN _ _ _ D A G _ _ hG U
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hL := GlobalTheory.allSixLaws.1
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaCompare.exists_nonzero_closed hL.secBaseChange D.toPre
  obtain ⟨σ, fam, h0, hE, hm, -⟩ := GlobalTheory.ThetaUnit.exists_theta hL.globalFns hL.secBaseChange le_rfl U th hth
  obtain ⟨g, hg, hn⟩ := GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl U.toUnifPre (hE 0) (h0 ▸ hth) hm
  exact ⟨DVR.secOfH0 σ, g, nonzeroLocus_firstPower_section_subset σ hn, hg⟩

end GlobalTheory.ThetaClosed
