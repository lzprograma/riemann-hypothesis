module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

noncomputable section

namespace GlobalTheory.RowEx

theorem keyFin_holds : KeyFin := by
  classical
  intro P Ξ hΞ
  let U : Key P := {p | p.1 ∈ Ξ ∧ {w | ¬ p.1.UnrAt w}.Finite ∧ ∀ w ∈ p.2, ¬ p.1.UnrAt w}
  have hU : U.Finite := by
    refine (hΞ.biUnion (t := fun ξ => {p ∈ U | p.1 = ξ}) fun ξ _ => ?_).subset fun p hp => Set.mem_biUnion hp.1 ⟨hp, rfl⟩
    by_cases hf : {w | ¬ ξ.UnrAt w}.Finite
    · refine ((hf.toFinset.powerset.finite_toSet).image fun Q => (ξ, Q)).subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact ⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun w hw => hf.mem_toFinset.2 (h.2.2 w hw)), rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact hf h.2.1
  refine ⟨{κ | κ ⊆ U}, hU.finite_subsets, ?_⟩
  rintro X T L μ₀ rfl hL h
  refine ⟨keyOf L, ?_, HEq.rfl⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, h1, h2⟩ := h t
  refine ⟨by rw [← eq_of_heq h2] at h1; exact h1, ?_, fun w hw => (hL.Q_ram t w).2 (Or.inl hw)⟩
  refine ((L.Q t).finite_toSet.union ((L.Q t).finite_toSet.image Formalism.DivisionValues.conjPl)).subset fun w hw => ?_
  rcases (hL.Q_ram t w).1 hw with h | ⟨w', h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨w', h, (GlobalTheory.GoodPrimes.isConjPl_iff.1 h').symm⟩

end GlobalTheory.RowEx
