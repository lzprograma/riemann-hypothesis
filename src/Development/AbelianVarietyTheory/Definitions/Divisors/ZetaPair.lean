module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HenQ

def eulerL (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    ((B w.1).map fun b => (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod

def eulerLd (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  eulerL K (fun w => (B w).map (·⁻¹)) S (1 - s)

end GlobalTheory.HenQ
