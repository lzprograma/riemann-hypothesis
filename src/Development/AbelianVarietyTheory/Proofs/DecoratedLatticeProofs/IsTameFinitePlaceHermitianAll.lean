module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.FinPl.TamePlaces

theorem extUnramAt (D : D7) (v : Pl D) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := by
  intro P hP _
  refine not_dvd_differentIdeal_iff.1 ?_
  rw [GlobalTheory.DensityEuler.differentIdeal_eq_top D.sp.cm]
  intro hd
  exact hP.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 hd))

theorem split_over_two (D : D7) (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) :
    ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, he, hc, hs, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same D.host.F v 1,
      fun v' hv' => GlobalTheory.SplitIdem.evalV_singleV_ne D.host.F v 1 hv'⟩
  exact ⟨e, _, ⟨he, hc, v, _, hε, hs⟩, hε, hs⟩

theorem tame : ∀ (D : D7) (v : Pl D), Tame D v := by
  intro D v
  refine ⟨extUnramAt D v, ?_⟩
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · exact Or.inr (split_over_two D v h2)
  · exact Or.inl h2

end GlobalTheory.FinPl.TamePlaces
