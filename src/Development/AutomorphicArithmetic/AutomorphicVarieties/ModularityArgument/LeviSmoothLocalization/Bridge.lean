module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open UpperTheory.Zero.LLC UpperTheory.V.Z.Gam GroundTheory.Global.SemiLocal

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def PlainIff : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) v,
    (∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) ↔
      TorAt π v ∧ ∀ s, SuppAt π v s → Unl (Ideal.absNorm v.asIdeal) s

def WinOfP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ π : CuspSub K n, ∃ t : ℝ, ∀ v,
    ((∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) → WinAt π t v) ∧
      ∀ B, (CG.mk π).HasSat v B → WinAt π t v

def SuppSmo1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (π π' : CuspSub K 1),
    (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B ∧ (CG.mk π').HasSat v B) →
    ∀ (t : ℝ) v, WinAt π t v → WinAt π' t v

theorem winOfP_of (hp : PlainIff) (h : WinOf) (hs : SphUnl) : WinOfP := by
  intro K _ _ _ n hn π
  obtain ⟨t, ht⟩ := h K n hn π
  exact ⟨t, fun v => ⟨fun a => ht v ((hp K n hn π v).1 a).1 ((hp K n hn π v).1 a).2,
    fun B hB => ht v (hs K n hn π v B hB).1 (hs K n hn π v B hB).2⟩⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
