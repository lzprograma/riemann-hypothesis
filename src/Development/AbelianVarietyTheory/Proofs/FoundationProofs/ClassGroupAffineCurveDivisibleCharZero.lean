module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.FunctionField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbedding
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CcSubst
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Lemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosed
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Polynomial.IsIntegral

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne, Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily, Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution, Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne", "h": "module\n\npublic import Mathlib.NumberTheory.FunctionField\npublic import Mathlib.RingTheory.SimpleRing.Principal\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc\nimport Mathlib.Algebra.AffineMonoid.UniqueSums\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle\npublic import Mathlib.RingTheory.Localization.NormTrace\n\n"}
section -- clump:auto
@[expose] public section

open Polynomial

namespace GlobalTheory


open Polynomial in
theorem _root_.GlobalTheory.exists_integral_norm_natDegree_mod_eq_one :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
      [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 1 ≤ N →
      ∃ f : FunctionField.ringOfIntegers k K, f ≠ 0 ∧ (Algebra.norm k[X] f).natDegree % N = 1 % N := by
  intro k K _ _ _ _ _ _ _ _ N hN
  set O := FunctionField.ringOfIntegers k K
  have hC1 : _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) := by
    unfold _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle
    intro n d f hf hd hdn
    obtain ⟨x, hx, h⟩ := _root_.GlobalTheory.tsenLang_ratFunc k n 1 d (fun _ => f) (fun _ => hf) hd (by simpa using hdn)
    exact ⟨x, hx, h 0⟩
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) K hC1
    RatFunc.X RatFunc.X_ne_zero
  haveI : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  haveI : Module.Free k[X] O := Module.free_of_finite_type_torsion_free'
  haveI := IsIntegralClosure.isLocalization k[X] (RatFunc k) K O
  have hnorm : ∀ a : O, algebraMap k[X] (RatFunc k) (Algebra.norm k[X] a) =
      Algebra.norm (RatFunc k) (algebraMap O K a) := fun a =>
    (Algebra.norm_localization k[X] (nonZeroDivisors k[X]) (Rₘ := RatFunc k) (Sₘ := K) a).symm
  obtain ⟨⟨a, s⟩, hxa⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid O (nonZeroDivisors k[X])) x
  obtain ⟨b, hb, hbs⟩ := s.2
  simp only at hxa
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set r := Module.finrank k[X] O
  have hs : Algebra.norm k[X] (s : O) = b ^ r := by rw [← hbs]; exact Algebra.norm_algebraMap b
  have ha : Algebra.norm k[X] a = X * b ^ r := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [hnorm, ← hxa, map_mul, hx, ← hnorm, hs, map_mul, RatFunc.algebraMap_X]
  have hexp : r + r * (N - 1) = r * N := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hf : Algebra.norm k[X] (a * (s : O) ^ (N - 1)) = X * b ^ (r * N) := by
    rw [map_mul, map_pow, ha, hs, mul_assoc, ← pow_mul, ← pow_add, hexp]
  refine ⟨a * (s : O) ^ (N - 1), ?_, ?_⟩
  · intro h
    have h0 := hf
    rw [h, Algebra.norm_zero] at h0
    exact mul_ne_zero X_ne_zero (pow_ne_zero _ hb0) h0.symm
  · rw [hf, natDegree_mul X_ne_zero (pow_ne_zero _ hb0), natDegree_X, natDegree_pow,
      show r * N * b.natDegree = r * b.natDegree * N by ring, Nat.add_mul_mod_self_right]

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily", "h": "module\n\npublic import Mathlib.RingTheory.PowerSeries.Derivative\npublic import Mathlib.RingTheory.PowerSeries.Basic\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution\npublic import Mathlib.RingTheory.PowerSeries.Substitution\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.CcSubst\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Polynomial

set_option linter.deprecated false

namespace GlobalTheory.DeformZeros

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

end GlobalTheory.DeformZeros

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution", "h": "module\n\npublic import Mathlib.FieldTheory.IsAlgClosed.Basic\npublic import Mathlib.RingTheory.DedekindDomain.Basic\npublic import Mathlib.RingTheory.PowerSeries.Substitution\npublic import Mathlib.RingTheory.PowerSeries.Derivative\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily\npublic import Mathlib.RingTheory.PowerSeries.Basic\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbedding\npublic import Mathlib.RingTheory.PowerSeries.Inverse\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosed\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Polynomial

namespace GlobalTheory.FormalDeform

theorem constantCoeff_subst_eq {k : Type} [Field k] (a φ : PowerSeries k)
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' hs,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd, smul_zero]

theorem not_mem_pow_succ {A : Type} [CommRing A] [IsDedekindDomain A] {N : ℕ} {I : Type}
    [Fintype I] {D P₀ : Ideal A} {Q : I → Ideal A} {f₀ : A} (hP₀ : P₀.IsMaximal)
    (hQmax : ∀ i, (Q i).IsMaximal) (hQinj : Function.Injective Q) (hQP : ∀ i, Q i ≠ P₀)
    (hDQ : ∀ i, ¬ D ≤ Q i) (hf₀ : f₀ ≠ 0)
    (hspan : Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N) (i : I) : f₀ ∉ Q i ^ (N + 1) := by
  apply GlobalTheory.PicDiv.FormalDeformHasse.not_mem_pow_succ <;> assumption

theorem coeff_map_sum {k A : Type} [Field k] [CommRing A] [Algebra k A] {m : ℕ}
    (σ : A →ₐ[k] PowerSeries k) (v : Fin m → A) (c : Fin m → k) (l : ℕ) :
    ∑ j, c j * PowerSeries.coeff l (σ (v j)) = PowerSeries.coeff l (σ (∑ j, c j • v j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

end GlobalTheory.FormalDeform
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle\npublic import Mathlib.FieldTheory.IsAlgClosed.Basic\npublic import Mathlib.RingTheory.ClassGroup.Basic\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosed\nimport Mathlib.Algebra.AffineMonoid.UniqueSums\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.FreeModule.Norm\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Polynomial.IsIntegral\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Polynomial

namespace GlobalTheory

theorem classGroup_ringOfIntegers_divisible : GlobalTheory.NeedB.ClDiv := by
  intro k K _ _ _ _ _ _ _ _ N hN c
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    exact ⟨c, (pow_one c).symm⟩
  set A := FunctionField.ringOfIntegers k K
  have : Algebra.IsSeparable (RatFunc k) K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  have : Module.Free k[X] A := IsIntegralClosure.module_free k[X] (RatFunc k) K _
  have : Module.Finite k[X] A := IsIntegralClosure.finite k[X] (RatFunc k) K _
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K _
  letI : Algebra k A := ((algebraMap k[X] A).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.exists_integral_norm_natDegree_mod_eq_one k K N hN
  have hdim : Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
    rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hf0]
    exact hf
  exact GlobalTheory.PicDiv.classGroup_nthPower_of_codim_one_mod k A N hN (GlobalTheory.PicDiv.exists_classGroup_mk0_eq_mul_pow_reduced k A (GlobalTheory.reduced_fibres_almost_all k A) N h (Nat.cast_ne_zero.2 (by omega))) ⟨f, hf0, hdim⟩ c

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero =====
