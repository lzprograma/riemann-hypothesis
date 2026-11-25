module

import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteSpanAlgebraMapOfFreeFinite
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.FlatComplete

theorem mem_smul_top_iff_repr {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι]
    (b : Module.Basis ι O M) (J : Ideal O) (x : M) :
    x ∈ J • (⊤ : Submodule O M) ↔ ∀ i, b.repr x i ∈ J := by
  first | exact _root_.GlobalTheory.CNorm.mem_smul_top_iff_repr | exact @_root_.GlobalTheory.CNorm.mem_smul_top_iff_repr | apply _root_.GlobalTheory.CNorm.mem_smul_top_iff_repr <;> assumption

theorem isAdicComplete_of_finite_basis {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Fintype ι] (b : Module.Basis ι O M) (J : Ideal O) [hO : IsAdicComplete J O] :
    IsAdicComplete J M := by
  have hR : ∀ (n : ℕ) (r : O), r ∈ (J ^ n • ⊤ : Submodule O O) ↔ r ∈ J ^ n := fun n r => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (J ^ n • ⊤ : Submodule O M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (J ^ n • ⊤ : Submodule O O)] := fun n x y => by
    simp only [SModEq.sub_mem, hR, mem_smul_top_iff_repr b (J ^ n), map_sub, Finsupp.sub_apply]
  rw [isAdicComplete_iff]
  refine ⟨isHausdorff_iff.2 fun x hx => ?_, isPrecomplete_iff.2 fun f hf => ?_⟩
  · apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus (inferInstance : IsHausdorff J O) _ fun n => ?_
    have := (key n x 0).1 (hx n) i
    rwa [map_zero, Finsupp.zero_apply] at this
  · have hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete J O) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    rw [← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]
    exact hL i n

theorem isAdicComplete_of_finite_flat (O : Type) [CommRing O] [IsLocalRing O] (J : Ideal O)
    (hO : IsAdicComplete J O) (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Flat O A] : IsAdicComplete (J.map (algebraMap O A)) A := by
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  have := hO
  exact (IsAdicComplete.map_algebraMap_iff (I := J) (M := A)).2
    (isAdicComplete_of_finite_basis (Module.Free.chooseBasis O A) J)

end GlobalTheory.FlatComplete
