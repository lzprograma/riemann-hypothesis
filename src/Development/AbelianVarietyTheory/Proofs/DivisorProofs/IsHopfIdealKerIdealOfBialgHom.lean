module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal_of_bialgHom (k A B : Type) [CommRing k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] (f : B →ₐc[k] A) : (kerIdeal f).IsHopfIdeal k := by
  refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
  · intro x hx
    exact (kerIdeal_le_ker_iff f (counitAlgHom k A)).2 (fun c => by simp) hx
  · intro x hx
    have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    have h : kerIdeal f ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k A)) := by
      refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
      have key : ∀ t : B ⊗[k] B, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
          algebraMap k _ (counit (R := k)
            (TensorProduct.lid k B (LinearMap.rTensor B (counit (R := k) (A := B)) t))) := by
        intro t
        induction t with
        | add x y hx hy => simp only [map_add (f := _), hx, hy]
        | tmul x y =>
          rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
            TensorProduct.lid_tmul, map_smul]
          erw [h0, h0]
          simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
            smul_smul, mul_comm]
      rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
        TensorProduct.lid_tmul, one_smul]
    exact h hx
  · intro x hx
    have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k A) := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      have ha' : counit (R := k) a = 0 := ha
      change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
      rw [← bialgHom_map_antipode]
      exact Ideal.mem_map_of_mem (f : B →ₐ[k] A) (by simp [RingHom.mem_ker, ha'])
    exact h hx

end GlobalTheory.PDiv
