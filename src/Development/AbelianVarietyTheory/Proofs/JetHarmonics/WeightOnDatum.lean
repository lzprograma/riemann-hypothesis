module

public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.WeightOnDatum

theorem weight_on_datum : ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ DomW (T.Q.Dw j) (wtA w) ∧ (w.LastPos → Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) ∧ 1 ≤ WeightAlgebra.DF w) ∧ (∀ τ, (T.Q.Dw j).mult τ ≤ D.R.r) ∧ Fintype.card (Lt1 (T.Q.Dw j)) ≤ 2 * D.R.f * D.R.r ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ Module.finrank ℚ D.host.E = 2 * D.R.f := by
  intro D T hP j hj w
  obtain ⟨hDF, -, hPsi, hN, hwt⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hP j hj w
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  obtain ⟨hp, hq, -⟩ := hP.2.2.2 j hj
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hj2 := hj.2
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]; omega
  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hp0 : 0 < (D.R.sigW j).1 := by
    simp only [Ranks.sigW]; omega
  have hlast : w.LastPos → ∀ t, 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := fun hw t =>
    hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine ⟨hDF, ?_, fun hw => ⟨?_, ?_⟩, fun τ => ?_, ?_, hf, by omega, hfr⟩
  · intro τ i i' h
    exact (dom_wtA w).1 τ h
  · intro τ hτ _
    obtain ⟨t, rfl⟩ := (hPsi τ).1 hτ
    have hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
      unfold Datum.mult
      have hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
      rw [ite_eq_left hτ', hp]
    rw [hmult, (hwt t _).1]
    unfold ext0
    rw [dite_eq_left (by omega)]
    exact hlast hw t
  · have ht : Nonempty D.what₂.Tau := by
      by_cases h : InPsi T.Q.H D.host.φ₀
      · obtain ⟨t, -⟩ := (hPsi _).1 h
        exact ⟨t⟩
      · obtain ⟨t, -⟩ := (hN _).1 h
        exact ⟨t⟩
    obtain ⟨t⟩ := ht
    unfold WeightAlgebra.DF WeightAlgebra.degP
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, w.aP τ i) + ∑ i, w.aM τ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
    refine le_trans ?_ (Nat.le_add_right _ _)
    exact le_trans (hlast hw t) (Finset.single_le_sum (f := fun i => w.aP t i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  · rw [← hr, Datum.mult]
    split_ifs <;> omega
  · refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]

end GlobalTheory.WeightOnDatum
