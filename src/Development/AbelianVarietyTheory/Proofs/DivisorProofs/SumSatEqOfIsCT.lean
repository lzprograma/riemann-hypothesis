module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ResW.SatWordAt

open GlobalTheory.LFun Formalism.UG

theorem esymm_add (A B : Multiset ℂ) (j : ℕ) :
    (A + B).esymm j = ∑ i ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm i.1 * B.esymm i.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [zero_add, Finset.sum_eq_single (0, j)]
    · simp [Multiset.esymm]
    · rintro ⟨a, b⟩ hab hne
      have hab' : a + b = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
      obtain _ | a := a
      · exact absurd (by simp [← hab']) hne
      · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
        simp
    · simp
  | cons a A ih =>
    have hrec : ∀ (s : Multiset ℂ) (k : ℕ), (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := fun s k => by
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
    have h0 : ∀ s : Multiset ℂ, s.esymm 0 = 1 := fun s => by simp [Multiset.esymm]
    obtain _ | j := j
    · simp [h0]
    · rw [Multiset.cons_add, hrec, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [hrec, h0, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

theorem satEig_add {q r s N : ℕ} (hq : q ≠ 0) (h : r + s = N) {C B : Multiset ℂˣ} (hC : C.card = r) (hB : B.card = s) (j : ℕ) :
    satEig q N (C + B) j = ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
      (q : ℂ) ^ (((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2) * (satEig q r C i.1 * satEig q s B i.2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hz : ∀ (A : Multiset ℂˣ) (k : ℕ), A.card < k → (A.map fun b : ℂˣ => (b : ℂ)).esymm k = 0 := fun A k hk => by
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hk)]
    simp
  rw [satEig, Multiset.map_add (f := _), esymm_add, Finset.mul_sum]
  symm
  refine Finset.sum_subset_zero_on_sdiff (fun i hi => ?_) (fun i hi => ?_) fun i hi => ?_
  · exact Finset.HasAntidiagonal.mem_antidiagonal.2 (Finset.mem_filter.1 hi).2
  · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
    have h3 := Finset.HasAntidiagonal.mem_antidiagonal.1 h1
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, h3, and_true, not_and_or, not_lt] at h2
    rcases h2 with h2 | h2
    · rw [hz C _ (by omega)]; simp
    · rw [hz B _ (by omega)]; simp
  · simp only [satEig]
    have e : ((j : ℂ) * (N - j)) / 2 = ((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2 +
      (i.1 * (r - i.1)) / 2 + (i.2 * (s - i.2)) / 2 := by ring
    rw [e, Complex.cpow_add _ _ hq', Complex.cpow_add _ _ hq']
    ring

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {v : HeightOneSpectrum (𝓞 E)} {N r s : ℕ}

variable {ϖ : v.adicCompletion E}


end GlobalTheory.ResW.SatWordAt

namespace GlobalTheory.ResW

end GlobalTheory.ResW

end
