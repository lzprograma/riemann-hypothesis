module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic

@[expose] public section

noncomputable section

namespace Formalism.KernelCokernelLengths

open Polynomial

def PowBinom : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) (u ε q : A) (b Y : ℕ), 1 ≤ ℓ → 1 ≤ Y →
    ∃ α β : A, (u * q ^ ℓ + (ℓ : A) * ε) ^ b = (ℓ : A) ^ (b - (Y - 1) / ℓ) * α + q ^ Y * β ∧
      β ∈ Ideal.span {(ℓ : A), q ^ ℓ} ^ (b - (Y - 1) / ℓ - 1)

def InvConst : Prop :=
  ∀ (K : Type) [Field K] (D : Type) [AddCommGroup D] [Module K D] (Fil : ℤ → Submodule K D),
    Antitone Fil → ∀ χ : K, (∀ i : ℤ, i ≠ 0 → χ ^ i ≠ 1) →
    ∀ (b η : ℕ) (w : ℤ → D),
      (∀ j : ℤ, -(b : ℤ) < j → j < -(η : ℤ) → Fil j = Fil (j + 1)) →
      (∀ i : ℤ, (χ ^ i - 1) • w i ∈ Fil (-i)) →
      (∀ i : ℤ, i ≠ 0 → w i ∈ Fil (-i)) ∧
        ∀ i : ℤ, i ≠ 0 → i < (b : ℤ) → w i ∈ Fil (-(η : ℤ))

def KerCoker : Prop :=
  ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M], Module.length O M ≠ ⊤ →
    ∀ (f : Module.End O M) (N : Submodule O M), N.map f ≤ N →
      Module.length O (↥N ⧸ (N.map f).comap N.subtype) ≤ Module.length O (LinearMap.ker f)

def TorsKer : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : O), ℓ ≠ 0 →
    ∀ n k : ℕ,
      Module.length O (LinearMap.ker (LinearMap.mulLeft O
        (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) ^ n, PowerSeries.C (ℓ ^ k)})
          ((PowerSeries.X : PowerSeries O) - PowerSeries.C ℓ)))) ≤
        (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def DetLen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (d : Module.End O M),
    LinearMap.det d ≠ 0 →
      Module.length O (M ⧸ LinearMap.range d) = Module.length O (O ⧸ Ideal.span {LinearMap.det d})

def hCoef (x : ℝ) : ℝ := x ^ 2 * (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)))

def HCoefLim : Prop :=
  AntitoneOn hCoef (Set.Ici 11) ∧ (∀ x : ℝ, 11 ≤ x → 25 ≤ hCoef x) ∧
    Filter.Tendsto hCoef Filter.atTop (nhds 25)

def ThickA : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b η S t bi h : ℕ), B₀ ≤ b →
    (η : ℝ) ≤ δ * b → (S : ℝ) ≤ δ * b → (t : ℝ) ≤ δ * b →
    b ≤ bi + t + 1 → bi + S ≤ h → h ≤ b + η + t + S + 1 →
    ((2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ + (η + t + 1) + 1 : ℕ) : ℝ) ≤ (0.42 + ε) * b

def ThickB : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b η S t bi h : ℕ), B₀ ≤ b →
    (η : ℝ) ≤ δ * b → (S : ℝ) ≤ δ * b → (t : ℝ) ≤ δ * b →
    b ≤ bi + t + 1 → bi + S ≤ h → h ≤ b + η + t + S + 1 →
    2 * (η + t + 1) ≤ h ∧ h ≤ 2 * bi ∧
      2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ + (η + t + 1) + 1 ≤ bi

def QPow : Prop :=
  ∀ (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ), (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r}

def LenSplit : Prop :=
  ∀ (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R] (π : Module.End O R)
    (R' R'' : Submodule O R), R' ≤ R'' →
      Module.length O (R ⧸ (R' ⊔ LinearMap.range π)) ≤
        Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) +
          Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype)

def TorsKerSum : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : O), ℓ ≠ 0 →
    ∀ (m k : ℕ) (n : Fin m → ℕ),
      Module.length O (LinearMap.ker (LinearMap.pi (fun j : Fin m =>
        (LinearMap.mulLeft O
          (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) ^ n j, PowerSeries.C (ℓ ^ k)})
            ((PowerSeries.X : PowerSeries O) - PowerSeries.C ℓ))).comp
          (LinearMap.proj (R := O) (φ := fun j : Fin m =>
            PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) ^ n j, PowerSeries.C (ℓ ^ k)}) j)))) ≤
        ((m * k : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def PdFacts : Prop :=
  ∀ (O : Type) [CommRing O] (V : Type) [AddCommGroup V] [Module O V] (d : Module.End O V)
    (P : O[X]) (M : Submodule O V), M.map d ≤ M →
    (aeval d (X * P) = 0 →
      (∀ v : V, d (aeval d P v) = 0) ∧ (∀ v : V, d v = 0 → aeval d P v = P.eval 0 • v) ∧
      ∀ w ∈ M, ∀ u : V, d u = w → P.eval 0 • w ∈ M.map d) ∧
    (aeval d P = 0 → ∀ u : V, d u ∈ M → P.eval 0 • u ∈ M)

end Formalism.KernelCokernelLengths
