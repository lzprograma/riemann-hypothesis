module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups

namespace Formalism.ConjugateSelfDual

section galois

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]

def UnramAt {R : Type*} [CommRing R] (ρ : G F Ω →* GL (Fin n) R) (v : HeightOneSpectrum (𝓞 F)) :
    Prop :=
  ∀ A, IsPlaceOver A v → ∀ σ ∈ Inertia A, ρ σ = 1

def FrobMatch (ρ : G F Ω →* GL (Fin n) (Qbar l)) (ι : Qbar l →+* ℂ)
    (P : HeightOneSpectrum (𝓞 F) → ℂ[X]) : Prop :=
  ∀ᶠ v in cofinite, ∀ A σ, IsPlaceOver A v → IsFrob A (normV v) σ →
    (ρ σ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι = P v

end galois

section polar

def conjGal {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (s : K ≃+* K) (τ : Ω ≃+* Ω)
    (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)) (σ : G K Ω) : G K Ω :=
  AlgEquiv.ofRingEquiv (f := (τ.symm.trans σ.toRingEquiv).trans τ) (by
    intro x
    have h1 : τ.symm (algebraMap K (Ω) x) =
        algebraMap K (Ω) (s.symm x) := by
      rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]
    simp only [RingEquiv.trans_apply, h1, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply])

variable {n l : ℕ} [Fact l.Prime]

end polar

structure CuspSpectrum (F : Type*) [Field F] [NumberField F] (n : ℕ) where
  Rep : Type
  wt : Rep → (F →+* ℂ) → Fin n → ℤ
  level : Rep → ℕ → Prop
  hecke : Rep → HeightOneSpectrum (𝓞 F) → ℂ[X]
  level_exists : ∀ π, ∃ M : ℕ, 0 < M ∧ level π M
  level_dvd : ∀ π (M M' : ℕ), level π M → M ∣ M' → 0 < M' → level π M'
  hecke_monic : ∀ π (M : ℕ) (v : HeightOneSpectrum (𝓞 F)), level π M →
    ((M : ℕ) : 𝓞 F) ∉ v.asIdeal → (hecke π v).Monic ∧ (hecke π v).natDegree = n
  mult_one : ∀ π π', (∀ᶠ v in cofinite, hecke π v = hecke π' v) → π = π'
  finite : ∀ (M : ℕ) (w : (F →+* ℂ) → Fin n → ℤ), {π | level π M ∧ wt π = w}.Finite

abbrev SpectrumFamily := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), CuspSpectrum F n

end Formalism.ConjugateSelfDual
