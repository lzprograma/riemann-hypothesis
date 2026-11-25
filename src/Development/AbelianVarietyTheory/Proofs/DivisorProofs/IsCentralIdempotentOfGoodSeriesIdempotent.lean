module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.GoodLatCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

structure PlaceIso (D : D7) (Pg : Finset (Pl D.host.E)) where
  pl : TypePl D ≃ ↥Pg
  iso : ∀ v : TypePl D, ZMod (D.host.g v.1) ≃+* kP (pl v).1

namespace PlaceIso

variable {D : D7} {Pg : Finset (Pl D.host.E)} (P : PlaceIso D Pg) {LL : Type} [Field LL]

end PlaceIso


open GlobalTheory.MemN.TypesInhab in
theorem goodSeriesIdempotent_central_idempotent (D : D7) :
    D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧ D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := TypePl D) (P := fun v => Fin D.R.r → ZMod (D.host.g v.1))
    (fun v p => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0 (fun g => rfl)
    (fun _ _ => D.ntypes.eSer_idem _ _) (fun _ _ => D.ntypes.eSer_central _ _)
    (fun _ p q hpq => D.ntypes.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, ?_⟩
  have h : D.ntypes.e0 = ∑ a : ∀ v : TypePl D, Fin D.R.r → ZMod (D.host.g v.1),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ten (fun v => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf (a v))) else 0 := by
    ext g
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine (finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl fun a _ => ?_)
    split_ifs <;> rfl
  conv_lhs => rhs; rw [h]
  rw [Finset.mul_sum]
  conv_rhs => rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [hm, ite_eq_left ha]
  · rw [mul_zero]

theorem isCentralIdempotent_of_goodSeriesIdempotent {D : D7} {LL : Type} [Field LL] (σ₀ : LL →+* ℂ) {eC : G0g D.nd → LL}
    (h : ∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g) : IsCentralIdem eC := by
  obtain ⟨hc, hi⟩ := goodSeriesIdempotent_central_idempotent D
  refine ⟨fun g x => σ₀.injective ?_, fun g => σ₀.injective ?_⟩
  · have := congrArg (fun z => z.coeff (x * g))
      (Subalgebra.mem_center_iff.1 hc (MonoidAlgebra.single x (1 : ℂ)))
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, inv_mul_cancel_left, one_mul, mul_one] at this
    rw [h, h, this]

  · rw [map_sum, h, ← hi, GlobalTheory.MemN.TypesInhab.coeff_mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_mul, h, h]

end GlobalTheory.GoodLatCompare
