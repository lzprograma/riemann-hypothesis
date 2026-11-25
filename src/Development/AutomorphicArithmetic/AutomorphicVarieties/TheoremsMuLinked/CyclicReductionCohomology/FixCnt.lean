module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CardEqPowLength
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaB
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem fixBd_abs {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)] {E S : Type} [AddCommGroup E] [Module A E] [Module.Finite A E]
    (f : S → E →ₗ[A] E) : ∃ C : ℕ, ∀ (m : ℕ) (E' : Type) [AddCommGroup E'] [Module A E'] (r : E →ₗ[A] E')
      (T : Set E'), LinearMap.ker r = IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E) →
      (∀ Y ∈ T, ∃ Z, r Z = Y ∧ ∀ s, r (f s Z) = 0) →
      T.ncard ≤ Nat.card (IsLocalRing.ResidueField A) ^
        (m * Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) + C) := by
  apply _root_.fixBd_abs <;> assumption

theorem UpperTheory.V.Th.fixCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (S : Type) (Φ : S → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O), ∃ C : ℕ, ∀ m, {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ s, red m (Φ s Y') = 0}.ncard ≤ Nat.card (ResidueField O) ^ (m * Module.finrank O (⨅ s, LinearMap.ker (Φ s) : Submodule O (Matrix (Fin n) (Fin n) O)) + C) := by
  intro l _ O _ _ _ hO _ n S Φ
  obtain ⟨-, hfin, -⟩ := hO
  obtain ⟨C, hC⟩ := fixBd_abs Φ
  refine ⟨C, fun m => hC m (Mm O n m) (Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).toLinearMap.mapMatrix _ ?_ fun Y hY => hY⟩
  ext Z
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    rw [Matrix.matrix_eq_sum_single Z]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h1 : Z i j ∈ maximalIdeal O ^ m := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h i) j)
    have e : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : O) := by simp
    rw [e]
    exact Submodule.smul_mem_smul h1 Submodule.mem_top
  · intro h
    refine Submodule.smul_induction_on h (fun a ha Y _ => ?_) fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ ha)
