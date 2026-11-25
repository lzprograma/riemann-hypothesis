module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift

theorem adjZ_eq_neg_of_mem_upq {p q : ℕ} {Z : Mat p q} (h : Z ∈ upq p q) : adjZ Z = -Z := by
  have h0 : Zᴴ * Jm p q + Jm p q * Z = 0 := h
  have h1 : Zᴴ * Jm p q = -(Jm p q * Z) := eq_neg_of_add_eq_zero_left h0
  rw [adjZ, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc,
    GlobalTheory.InvPairingTensor.Jm_mul_self, Matrix.one_mul]

theorem finiteSupport_of_admissible :
    ∀ (p q r s : ℕ) (T : GrpData r s) (R : DSRep T), Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → FiniteSupport p q R := by
  intro p q r s T R hA A _ _ B hB P
  refine GlobalTheory.InvPairingTensor.exists_finiteDimensional_kill R hA B (fun Z hZ Q y => ?_) P
  rw [hB Z Q y, adjZ_eq_neg_of_mem_upq hZ, map_neg, LinearMap.neg_apply, map_neg, neg_add_cancel]

end GlobalTheory.Chain.IoLift
