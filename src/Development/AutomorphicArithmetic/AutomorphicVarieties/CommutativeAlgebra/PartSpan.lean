module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.part_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R) (S : Set (W.σ →₀ ℕ)) (j : X), (∀ n ∈ S, Finsupp.weight W.wt n = j) →
      ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ S ∧ ∀ f : MvPowerSeries W.σ O, (∀ n, n ∉ S → coeff n f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O W.wt 0) ∧ f = ∑ m ∈ μ, b m * monomial m 1 := by
  intro O R _ _ _ X _ _ _ W S j hS
  classical
  haveI := W.fin
  have hMfin : {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  have hex : ∀ n ∈ S, ∃ m ∈ {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}, m ≤ n := by
    intro n hn
    obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
    exact ⟨b, hmin, hb⟩
  choose! c hcM hcle using hex
  refine ⟨hMfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact fun m hm => hm.1
  · intro f hf
    obtain ⟨b, hb⟩ : ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, ∀ m k,
        coeff k (b m) = if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0 :=
      ⟨fun m k => if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
    refine ⟨b, ?_, ?_⟩
    · intro m k hk
      rw [hb, ite_eq_right]
      rintro ⟨h1, h2⟩
      apply hk
      have hm : Finsupp.weight W.wt m = j := hS m (by rw [← h2]; exact (hcM _ h1).1)
      have hkm := hS _ h1
      rw [map_add (f := _), hm] at hkm
      simpa using hkm
    · ext n

      rw [map_sum, Finset.sum_congr rfl
      (g := fun m => if c n = m then (if n ∈ S then coeff n f else 0) else 0), Finset.sum_ite_eq]
      · by_cases hn : n ∈ S
        · rw [ite_eq_left ((Set.Finite.mem_toFinset hMfin).2 (hcM n hn)), ite_eq_left hn]
        · rw [hf n hn]
          simp
      · intro m _
        rw [MvPowerSeries.coeff_mul_monomial, mul_one]
        by_cases hmn : m ≤ n
        · rw [ite_eq_left hmn, hb, tsub_add_cancel_of_le hmn]
          by_cases h1 : n ∈ S <;> by_cases h2 : c n = m <;> simp [h1, h2]
        · rw [ite_eq_right hmn]
          by_cases h1 : n ∈ S
          · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
            simp [h3]
          · simp [h1]
