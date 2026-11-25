module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
open IsDedekindDomain

namespace GlobalTheory.FinClsLoc

theorem ratInt_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  apply _root_.GlobalTheory.FinClsLoc.eventually_rat_mem_adicCompletionIntegers <;> assumption

theorem ratInt_eventually_away {p : ℕ} (x : ℚ) :
    ∀ᶠ w : AwayP p in Filter.cofinite,
      algebraMap ℚ (w.1.adicCompletion ℚ) x ∈ w.1.adicCompletionIntegers ℚ :=
  (Subtype.val_injective.tendsto_cofinite).eventually (ratInt_eventually x)

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ C)
  (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply' (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul' (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem intC_stab : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), ∀ᶠ w : AwayP p in Filter.cofinite,
    (∀ a b : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w b → IntC G w (a * b)) ∧
    (∀ a : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w (starT G.star (w.1.adicCompletion ℚ) a).unop) ∧
    IntC G w (inC G (w.1.adicCompletion ℚ) (β : G.C)) ∧ IntC G w (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β
  set bb := Module.finBasis ℚ G.C
  have hc : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C) ×
      Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (bb t.1 * bb t.2.1) t.2.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hs : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (G.star (bb t.1)).unop t.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hb : ∀ x : G.C, ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ :=
    fun x => Filter.eventually_all.2 fun k => ratInt_eventually_away _
  have hin : ∀ (w : AwayP p) (x : G.C), (∀ k, algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈
      w.1.adicCompletionIntegers ℚ) → IntC G w (inC G (w.1.adicCompletion ℚ) x) := by
    intro w x hx k
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr ((1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] x) k ∈ _
    rw [repr_tmul_apply', one_mul]
    exact hx k
  filter_upwards [hc, hs, hb (β : G.C), hb ((β⁻¹ : G.Cˣ) : G.C)] with w hcv hsv hbv hbv'
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_, hin w _ hbv, hin w _ hbv'⟩
  · change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr (y * z) k ∈ _

    rw [eq_sum_tmul' bb w.1 y, eq_sum_tmul' bb w.1 z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_

    rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply']
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : Fin (Module.finrank ℚ G.C) → (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ᵐᵒᵖ),
        (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : w.1.adicCompletion ℚ ⊗[ℚ] G.C ≃+ _).symm f Finset.univ
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr _ k ∈ _

    rw [eq_sum_tmul' bb w.1 y, map_sum, hu, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply']
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.FinClsLoc
