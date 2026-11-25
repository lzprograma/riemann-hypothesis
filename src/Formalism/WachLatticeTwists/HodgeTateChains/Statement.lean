module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

def rI (ℓ m : ℕ) (U : Finset ℤ) (i : ℤ) : ℕ := ∑ u ∈ U.erase i, (m + padicValInt ℓ (u - i))

def cM (ℓ m : ℕ) (U : Finset ℤ) (a b : ℤ) : ℕ := ∑ i ∈ Finset.Ico a b, (2 + max 1 (rI ℓ m U i))

def cLL (ℓ m : ℕ) (U : Finset ℤ) (a b : ℤ) (d : ℕ) : ℕ := padicValNat ℓ d + cM ℓ m U a b

def c0 (ℓ m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt ℓ u)

def cTBof (ℓ s e gK c : ℕ) : ℕ :=
  c + (e + 2) * s + padicValNat ℓ e + e / (ℓ - 1) + 1 + (s + padicValNat ℓ (e + 1)) + gK

def cTB (ℓ s m e gK : ℕ) (U : Finset ℤ) : ℕ :=
  cTBof ℓ s e gK (cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)))

def TorsKilled (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [AddCommGroup A] [Module ℤ_[ℓ] A] (c : ℕ) : Prop :=
  ∀ x : A, (∃ k : ℕ, ((ℓ : ℤ_[ℓ]) ^ k) • x = 0) → ((ℓ : ℤ_[ℓ]) ^ c) • x = 0

def HTpoly (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Polynomial ℤ_[ℓ] :=
  ∏ a ∈ U, (X - C (((w ^ (i - a) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
