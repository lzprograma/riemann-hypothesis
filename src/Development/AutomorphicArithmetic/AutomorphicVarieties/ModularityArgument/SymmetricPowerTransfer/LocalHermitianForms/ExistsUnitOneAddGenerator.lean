module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.H90
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LcountNorm
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

@[expose] public section

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem IsLoc.two_ne (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have := (L.two.map (algebraMap O K)).ne_zero
  rwa [map_ofNat] at this

theorem lcount_inv (L : IsLoc O Δ) {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

theorem dat_move (L : IsLoc O Δ) {c : K} {d m : EL Δ τ} (h : IsDat c d m) {d₀ : EL Δ τ} (h₀ : d₀ * sigL d₀ = ofE Δ (ω : Etau K τ)) :
    ∃ m', IsDat c d₀ m' ∧ ∀ t : K, lcount O c d (t • m) = lcount O c d₀ (t • m') := by
  have h1 : (ω : Etau K τ) * (algebraMap K (Etau K τ) τ - ω) = 1 := by
    ext <;> simp
  have hω : IsUnit (ofE Δ (ω : Etau K τ)) := by
    refine isUnit_iff_exists_inv.2 ⟨ofE Δ (algebraMap K (Etau K τ) τ - ω), ?_⟩
    rw [← ofE_mul, h1]
    ext <;> simp [ofE]
  have hd : IsUnit d := isUnit_of_mul_isUnit_left (h.d_norm ▸ hω)
  obtain ⟨u, hu⟩ := hd
  have hβ : ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀ * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀) = 1 := by
    have hn := h.d_norm
    rw [← hu] at hn
    calc ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀ * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀)
        = ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (d₀ * sigL d₀) := by
          rw [sigL_mul]; ring
      _ = ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * ((u : EL Δ τ) * sigL (u : EL Δ τ)) := by
          rw [h₀, hn]
      _ = (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (u : EL Δ τ)) * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (u : EL Δ τ)) := by
          rw [sigL_mul]; ring
      _ = 1 := by simp [sigL_one]
  obtain ⟨y, hy⟩ := h90 O K Δ τ L h.reg _ hβ
  have key : d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = d₀ := by
    rw [hy, ← hu]
    calc (u : EL Δ τ) * (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀ * (y : EL Δ τ)) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)
        = ((u : EL Δ τ) * ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) * d₀ * ((y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) := by
          ring
      _ = d₀ := by simp
  refine ⟨m * y * star (sigL (y : EL Δ τ)), ?_, fun t => ?_⟩
  · have hD := (datIso O K Δ τ c d m y).2 h
    rwa [key] at hD
  · have e := (datIso O K Δ τ c d (t • m) y).1
    rw [key, smul_mul_assoc, smul_mul_assoc] at e
    exact e

theorem tri (L : IsLoc O Δ) (τ₀ : O) : τ₀ - 2 ∈ IsLocalRing.maximalIdeal O ∧ IsUnit (2 + τ₀) ∨ τ₀ + 2 ∈ IsLocalRing.maximalIdeal O ∧ IsUnit (2 - τ₀) ∨
    IsUnit (2 + τ₀) ∧ IsUnit (2 - τ₀) := by
  have h4 : IsUnit (4 : O) := by
    have h := L.two.mul L.two
    norm_num at h
    exact h
  have unit_of : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → IsUnit (4 + x) := by
    intro x hx
    by_contra hn
    have h1 : 4 + x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h2 : (4 : O) ∈ IsLocalRing.maximalIdeal O := by
      simpa using (IsLocalRing.maximalIdeal O).sub_mem h1 hx
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 h4
  by_cases ha : τ₀ - 2 ∈ IsLocalRing.maximalIdeal O
  · left
    refine ⟨ha, ?_⟩
    have h := unit_of _ ha
    convert h using 1
    ring
  · by_cases hb : τ₀ + 2 ∈ IsLocalRing.maximalIdeal O
    · right; left
      refine ⟨hb, ?_⟩
      have h := unit_of _ ((IsLocalRing.maximalIdeal O).neg_mem hb)
      convert h using 1
      ring
    · right; right
      refine ⟨?_, ?_⟩
      · have h := IsLocalRing.notMem_maximalIdeal.mp hb
        convert h using 1
        ring
      · have h := (IsLocalRing.notMem_maximalIdeal.mp ha).neg
        convert h using 1
        ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem EvenVal.of_mul_unit {c : K} {u : O} (hu : IsUnit u) (h : EvenVal O (c * algebraMap O K u)) : EvenVal O c := by
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨w, s, hs, he⟩ := h
  refine ⟨w * v⁻¹, s, hs, ?_⟩
  have hv : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc c = c * algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) := by
        rw [mul_assoc, hv, mul_one]
    _ = _ := by
        rw [he, Units.val_mul, map_mul]
        ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_unit_one_add_generator (hτ : τ ^ 2 - 4 ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω := by
  have h2 : 2 + τ ≠ 0 := by
    intro h
    apply hτ
    have e : τ = -2 := by linear_combination h
    rw [e]
    norm_num
  refine ⟨⟨1 + ω, ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩, ?_, ?_⟩, rfl⟩
  · ext <;> simp <;> field_simp <;> ring
  · ext <;> simp <;> field_simp <;> ring

theorem exists_a : ∃ a : (Etau K τ)ˣ, (a : Etau K τ) = ω := by
  have h1 : (ω : Etau K τ) * (algebraMap K (Etau K τ) τ - ω) = 1 := by
    ext <;> simp
  exact ⟨⟨ω, algebraMap K (Etau K τ) τ - ω, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end UpperTheory.V.Z.Sym.Loc
