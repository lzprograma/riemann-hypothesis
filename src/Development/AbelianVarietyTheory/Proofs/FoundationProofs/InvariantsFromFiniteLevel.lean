module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem charZero_of_tower (T : Tower p Ω) : CharZero Ω := by
  have hpp : p.Prime := Fact.out
  have hp : (p : Ω) ≠ 0 := by
    intro h0
    haveI : CharP Ω p := (CharP.charP_iff_prime_eq_zero hpp).mpr h0
    have hz := T.prim 1
    rw [pow_one] at hz
    have h1 : (T.ζ 1 - 1) ^ p = 0 := by rw [sub_pow_char, one_pow, hz.pow_eq_one, sub_self]
    have h2 : T.ζ 1 = 1 := sub_eq_zero.mp (pow_eq_zero_iff hpp.ne_zero |>.mp h1)
    rw [h2] at hz
    exact hpp.one_lt.ne' (hz.eq_orderOf.trans orderOf_one)
  let f : ℤ_[p] →+* Ω :=
    (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp (algebraMap ℤ_[p] (Lau p)))
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.one_lt.ne'
  have hu : IsUnit (((m : ℤ) : ℤ_[p])) := by
    refine PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm ?_))
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
  have hmu : IsUnit (m : Ω) := by
    have := hu.map f
    simpa using this
  push_cast at hn
  rcases mul_eq_zero.mp hn with h | h
  · exact hp (pow_eq_zero_iff' |>.mp h).1
  · exact hmu.ne_zero h

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_eq_pow (T : Tower p Ω) (i d : ℕ) : T.qq i = T.qq (i + d) ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ih, ← T.qpow (i + d), ← pow_mul, ← pow_succ', add_assoc]

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem sum_fixed (H : Subgroup (Gal p Ω)) (E : Finset (Gal p Ω)) (y₀ x : Ω)
    (hEH : ∀ g ∈ E, g ∈ H)
    (huniq : ∀ h ∈ H, ∃! g, g ∈ E ∧ h y₀ = g y₀ ∧ ∀ s ∈ ({x} : Finset Ω), h s = g s) :
    ∀ h ∈ H, h (∑ g ∈ E, g (y₀ * x)) = ∑ g ∈ E, g (y₀ * x) := by
  classical
  simp only [Finset.mem_singleton, forall_eq] at huniq
  let rep : Gal p Ω → Gal p Ω := fun a => if ha : a ∈ H then (huniq a ha).exists.choose else 1
  have hrep : ∀ a ∈ H, rep a ∈ E ∧ a y₀ = rep a y₀ ∧ a x = rep a x := by
    intro a ha
    simp only [rep, dite_eq_left ha]
    exact (huniq a ha).exists.choose_spec
  have hun : ∀ a ∈ H, ∀ g ∈ E, a y₀ = g y₀ → a x = g x → rep a = g := by
    intro a ha g hg h1 h2
    exact ((huniq a ha).unique (hrep a ha) ⟨hg, h1, h2⟩)
  intro h hh

  rw [map_sum]
  have hmem : ∀ g ∈ E, h * g ∈ H := fun g hg => H.mul_mem hh (hEH g hg)
  have hmem' : ∀ g ∈ E, h⁻¹ * g ∈ H := fun g hg => H.mul_mem (H.inv_mem hh) (hEH g hg)
  refine Finset.sum_bij' (fun g _ => rep (h * g)) (fun g _ => rep (h⁻¹ * g))
    (fun g hg => (hrep _ (hmem g hg)).1) (fun g hg => (hrep _ (hmem' g hg)).1) ?_ ?_ ?_
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    refine hun _ (hmem' _ (hrep _ (hmem g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem' g hg)
    refine hun _ (hmem _ (hrep _ (hmem' g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    show (h * g) (y₀ * x) = _
    rw [map_mul, map_mul (rep (h * g)), h1, h2]

end GlobalTheory.K5.FinLevel
