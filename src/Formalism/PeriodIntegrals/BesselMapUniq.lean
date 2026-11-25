module

public import Formalism.PeriodIntegrals.IsLowUnitH
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FormalDegreeBessel.StatementDS
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace PI.BesselMapUniq

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open PI.UpqRep

section Bessel

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

end Bessel

section Smooth

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def IsBesselMapSm {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (B : H → Wp) : Prop :=
  (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B (v + w) = B v + B w) ∧
    (∀ (c : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, B (c • v) = c • B v) ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      B (σ (h * m) v) = ψ m • π h (B v)) ∧
    IsCWCont (k := k) (r := r) σ B

end Smooth

end PI.BesselMapUniq
