module

public import Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

def opDeg {ι : Type} {a : ℕ} (lam : ι → DomWeight a) (n : ι → ℕ) (τ : ι) : ℕ := ∑ r, ((lam τ).natW r + n τ)

def stepDeg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) (i : ℕ) : X.Tau → ℕ := opDeg (W.lamTrue u i) (nuLast W u i)

def StepDegIs : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (u : Pr.Word) (i : ℕ), i < R.m → ∀ τ : X.Tau,
    ((stepDeg W u i τ : ℕ) : ℤ) = ∑ r, (W.nuW u (i + 1) τ).w r

section Inst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

def ThHypD : Prop :=
  (∀ i, i ≤ m2 → ThEquivP ((chThT W Ch sel mu cst A u m2).th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho) ∧
  ThEquivP (chThT W Ch sel mu cst A u m2).top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho

end Inst

end Formalism.L2.Ker
