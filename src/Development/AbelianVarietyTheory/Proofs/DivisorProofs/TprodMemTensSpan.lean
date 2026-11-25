module

public import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

def chiOne (P Q R S : ℕ) (x : ℚ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ X : {X : Mat P Q // IsKC X}, LinearMap.ker (fockAct1 P Q R S X.1 - ((x : ℂ) * X.1.trace) • 1)

theorem mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ chiOne P Q R S x ↔ ∀ X : Mat P Q, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f := by
  simp only [chiOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

def tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V) :
    Submodule ℂ (⨂[ℂ] _ : ι, V) :=
  Submodule.span ℂ {T | ∃ f : ι → V, (∀ w, f w ∈ H w) ∧ T = PiTensorProduct.tprod ℂ f}

theorem tprod_mem_tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V)
    (f : ι → V) (hf : ∀ w, f w ∈ H w) : PiTensorProduct.tprod ℂ f ∈ tensSpan H :=
  Submodule.subset_span ⟨f, hf, rfl⟩

end GlobalTheory.KFixIrr

end
