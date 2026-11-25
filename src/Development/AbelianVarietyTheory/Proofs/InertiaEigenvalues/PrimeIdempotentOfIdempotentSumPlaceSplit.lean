module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Classical

namespace GlobalTheory.IdemSumBranch

open GlobalTheory.StdFrames GlobalTheory.IdemSupport

variable {D : D7}

theorem cpt_idemSum {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {Q : Pl D.host.E} (hQ : Q ∈ S) :
    cpt Q (toEAf D ea) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hs := map_sum ((cpt Q).comp (toEAf D)).toAddMonoidHom es S
  refine hs.trans ?_
  rw [Finset.sum_eq_single_of_mem Q hQ]
  · exact (cpt_of_isIdemAt (hes Q hQ)).1
  · intro R hR hne
    exact (cpt_of_isIdemAt (hes R hR)).2 Q hne.symm

theorem conjPrime_ne {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {P Q : Pl D.host.E} (hP : P ∈ S)
    (hQ : Q ∈ S) : cP Q ≠ P := by
  intro hc
  have h1 := congrArg (fun t => cpt P (toEAf D t)) h.2
  simp only [RingHom.map_mul, RingHom.map_zero, cpt_idemSum h hP, one_mul] at h1
  rw [toEAf_cA, ← hc] at h1
  have h2 := cpt_sg_eq_zero h1
  rw [sg_sg, cpt_idemSum h hQ] at h2
  exact one_ne_zero h2

end GlobalTheory.IdemSumBranch
