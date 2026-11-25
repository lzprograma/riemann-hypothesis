module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem polZ_mem {l : ℕ} [Fact l.Prime] (F : GFrame l) {γ : F.Γ} (h : γ ∉ F.η.ker) : γ * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at h ⊢
  rw [map_mul, F.η_c, (Int.units_eq_one_or (F.η γ)).resolve_left h]
  simp

private theorem polZ_nmem {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : (g : F.Γ) * F.c ∉ F.η.ker := by
  have := g.2
  rw [MonoidHom.mem_ker] at this ⊢
  rw [map_mul, F.η_c, this]
  decide

private theorem polZ_proj {l : ℕ} [Fact l.Prime] (F : GFrame l) :
    ∃ p : F.Γ → F.G₀, Continuous p ∧ (∀ g : F.G₀, p g = g) ∧ ∀ g : F.G₀, p (g * F.c) = g := by
  apply _root_.polZ_proj <;> assumption

private theorem polZ_cases {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, polZ_mem F h⟩, ?_⟩
    show γ = γ * F.c * F.c
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) :
    (F.conj g : F.Γ) = F.c * g * F.c := by
  show F.c * g * F.c⁻¹ = _
  rw [inv_eq_of_mul_eq_one_right F.c_sq]

private theorem polZ_ext {l : ℕ} [Fact l.Prime] (F : GFrame l) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (rep : Representation A F.Γ M) (Z : F.G₀ → M) (hl : IsLocallyConstant Z)
    (hm : ∀ g h, Z (g * h) = Z g + rep g (Z h)) (hc : ∀ g, Z (F.conj g) = rep F.c (Z g)) :
    ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = Z g := by
  apply _root_.polZ_ext <;> assumption

theorem UpperTheory.V.Th.polP :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (P : Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (rep : Representation A F.Γ (Matrix (Fin n) (Fin n) R)), IsUnit P → IsAdP F ρ P χ rep → (∀ z : F.G₀ → Matrix (Fin n) (Fin n) R, IsLocallyConstant z → (∀ g g', z (g * g') = z g + χ g • (ρ g * z g' * ρ g⁻¹)) → (∀ g, P * z (F.conj g) = -(χ F.c • ((z g)ᵀ * P))) → ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = z g) ∧ (∀ y ∈ Zl rep, y F.c = 0 → (∀ g : F.G₀, P * y (F.conj g) = -(χ F.c • ((y g)ᵀ * P))) ∧ ((∀ g : F.G₀, y g = 0) → y = 0)) := by
  intro l _ F A R _ _ _ n ρ P χ rep hP ⟨a1, a2⟩
  refine ⟨fun z hl hm hc => ?_, fun y ⟨_, hy⟩ hc => ⟨fun g => ?_, fun h0 => ?_⟩⟩
  · exact polZ_ext F rep z hl (fun g h => by rw [a1]; exact hm g h)
      (fun g => hP.mul_left_cancel (by rw [a2]; exact hc g))
  · rw [← a2, polZ_conj, hy, hc, map_zero, add_zero, hy, hc, zero_add]
  · funext γ
    rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact h0 g
    · rw [hy, h0, hc, map_zero, add_zero]
      rfl
