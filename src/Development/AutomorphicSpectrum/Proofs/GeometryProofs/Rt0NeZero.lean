module

import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PsiCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem rt0_conj_neg_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.rt0_conj_neg_ne_zero

theorem rt0_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have hsq := H.sqrt_neg_disc_sq
  rw [h] at hsq
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  simp at hsq
  exact H.d_prime.ne_zero hsq

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
