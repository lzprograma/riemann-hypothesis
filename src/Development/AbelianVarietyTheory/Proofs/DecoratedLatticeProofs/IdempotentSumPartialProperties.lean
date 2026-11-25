module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PartialIdemSum

theorem mul_sum_of_isIdemAt {D : D7} {x : AE D} {P : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x P) (S : Finset (Formalism.L2.DIV.Pl D.host.E)) (f : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P' ∈ S, Formalism.L2.NTheta.IsIdemAt (f P') P') :
    x * ∑ P' ∈ S, f P' = if P ∈ S then x else 0 := by
  rw [Finset.mul_sum]
  split_ifs with hP
  · rw [Finset.sum_eq_single P]
    · have h1 := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P) P P hx (hf P hP)).1 rfl
      rw [← h1]; exact hx.1.1
    · intro P' hP' hne
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 (Ne.symm hne)
    · intro h; exact absurd hP h
  · refine Finset.sum_eq_zero fun P' hP' => ?_
    refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 ?_
    rintro rfl; exact hP hP'

theorem sum_mul_sum_of_subset {D : D7} (S S' : Finset (Formalism.L2.DIV.Pl D.host.E)) (f g : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P ∈ S, Formalism.L2.NTheta.IsIdemAt (f P) P) (hg : ∀ P ∈ S', Formalism.L2.NTheta.IsIdemAt (g P) P) (hS : S ⊆ S') :
    (∑ P ∈ S, f P) * ∑ P ∈ S', g P = ∑ P ∈ S, f P := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [mul_sum_of_isIdemAt (hf P hP) S' g hg, ite_eq_left (hS hP)]

end GlobalTheory.PartialIdemSum
