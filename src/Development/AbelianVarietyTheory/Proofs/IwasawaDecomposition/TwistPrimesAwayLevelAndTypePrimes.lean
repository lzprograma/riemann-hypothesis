module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Formalism.LocalToGlobal.Columns.BaseLemmas
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TwistPrimes

open GlobalTheory.Mem.LevTwist ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem twist_primes_away : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  intro B X I h
  refine ⟨I.twistPrimes_reference_tuple_eq_empty, fun u a P hP => ?_⟩
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hg := good_of_mem h (I.Q_subset_SQ a hP)
  have hS := hg.2.2.2
  have hu : (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := (under_eq_iff B.host P _).2 (Or.inr rfl)
  have hT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      ((B.primes X).T u : 𝓞 B.host.E) ∉ R.asIdeal := fun R hR hm => hS (by
    rw [← hR, (ReadTwist.plc_under_eq_iff (F := B.host.F) R (hPr.T_prime u)).2 hm]
    exact h.T_mem u)
  have hpi : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      (B.primes X).piT u ∉ R.asIdeal := fun R hR hm => hT R hR (by
    rw [← hPr.piT_norm u]; exact Ideal.mul_mem_right _ _ hm)
  have h0 : (B.primes X).piT u ≠ 0 := fun e => by
    have := hPr.piT_norm u
    rw [e, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hvT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vT u := fun R hR hm => hpi R hR ((mem_divs h0 _).1 hm)
  have hvG : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vGs := fun R hR hm => hS (by rw [← hR]; exact plc_mem h hm)
  refine ⟨⟨hvT P rfl, hvG P rfl, hvT _ hu, hvG _ hu, fun hc => ?_⟩, hpi P rfl, fun hm => hT P rfl ?_⟩
  · have e := (good_of_mem h (I.Q_subset_SQ a hc)).1
    rw [hu, hg.1] at e
    exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 hg.2).1 e.symm
  · rw [← map_natCast (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))]
    exact hm

end GlobalTheory.Mem.Col2.TwistPrimes
