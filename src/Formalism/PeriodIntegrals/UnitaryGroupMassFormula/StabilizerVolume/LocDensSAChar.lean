module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

@[expose] public section
noncomputable section
open NumberField
namespace PI.VolStabS

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnot χ hχ hΛ x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  suffices h : (ℓ : InfiniteAdeleRing F → ℂ) = fun _ => 0 by rw [hℓ, congrFun h x, Complex.exp_zero]
  apply (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hℓc continuous_const
  funext a
  let p : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hp : p ≠ 0 := by simp [p, Real.pi_ne_zero, Complex.I_ne_zero]
  apply (mul_eq_zero.mp ?_).resolve_left (inv_ne_zero hp)
  refine hA F Λ hne hnot ((AddMonoidHom.mulLeft p⁻¹).comp
    (ℓ.comp (algebraMap F (InfiniteAdeleRing F)).toAddMonoidHom)) (fun b hb => ?_) a
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ((hℓ _).symm.trans (hΛ b hb))
  exact ⟨n, (inv_mul_eq_iff_eq_mul₀ hp).2 (hn.trans (mul_comm _ p))⟩

end PI.VolStabS
