module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af

def infOf {n : ℕ} (m : Fin n → ℤ) : Multiset ℂ := Finset.univ.val.map fun i => ((n : ℂ) - 1) / 2 + (m i : ℂ)

def SigK (K : Type) [Field K] [NumberField K] [IsCMField K] {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (CuspSub K n) :=
  {π | (∀ τ, π.HasInfChar τ (infOf m)) ∧ GlobalTheory.ContraPair.DualIsConj π ∧ HasFixed π.finPart (KLev K n M)}

def CardK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (CuspSub K n), (∀ π ∈ S, π ∈ SigK K m M) → (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
        S.card ≤ c * (M * (H + 1)) ^ A

def ConjK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (σ : ℂ ≃+* ℂ), ∀ π ∈ SigK K m M, ∃ π' ∈ SigK K m M, ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ

def SatK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n M : ℕ) (π : CuspSub K n), HasFixed π.finPart (KLev K n M) →
    ∀ w : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ w.asIdeal → ∃ B, (CG.mk π).HasSat w B

def SlopesIn {n : ℕ} (q : ℕ) (m : Fin n → ℤ) (B : Multiset ℂ) : Prop :=
  ∀ b ∈ B, (∀ a : ℤ, (∀ i, -a ≤ m i) → IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)) ∧
    ∀ a : ℤ, (∀ i, m i ≤ a) → IsIntegral ℤ ((q : ℂ) ^ a * b)

def IntK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigK K m M, ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M →
      ¬ (p : ℤ) ∣ discr K → ∀ B, (CG.mk π).HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def IsoOfFrob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' →
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) → RepIso r r'

end UpperTheory.V.Af
