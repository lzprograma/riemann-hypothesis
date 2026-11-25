module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
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

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

abbrev Levels (E : Type) [Field E] [NumberField E] (a : ℕ) : Type :=
  ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin a) (w.adicCompletion E))

structure LocOps (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (Kw : Levels E a) (J : Type) where

  pl : J → HeightOneSpectrum (𝓞 E)
  split : ∀ j, IsSplitAt (pl j)
  away : ∀ j, ((l : ℕ) : 𝓞 E) ∉ (pl j).asIdeal

  f : ∀ j, GL (Fin a) ((pl j).adicCompletion E) →₀ ℂ
  int : ∀ j g, ‖ι.symm (f j g)‖ ≤ 1

  z : ∀ j, SmIrr (GL (Fin a) ((pl j).adicCompletion E)) → ℂ
  act : ∀ j σ, ∀ v ∈ PRep.fixed σ.ρ (Kw (pl j)), opOf σ.ρ (f j) v = z j σ • v

def SphOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ),
    (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥ → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ n : ℤ, ∃ f : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV w : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)), opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV w) B).map (· ^ n)).sum • v

structure Up (Ω : Type) [Field Ω] (l : ℕ) {E M : Type} [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [Field M] [NumberField M]
    [IsCMField M] [Algebra M Ω] [Algebra E M] [IsScalarTower E M Ω] {a : ℕ} (π : CuspSub E a) (π' : CuspSub M a) : Prop where
  scope : ∀ l' : ℕ, InScope .csd l' π (quadChar E ^ a) → InScope .csd l' π' (quadChar M ^ a)
  self : InScope .csd l π (quadChar E ^ a)
  inf : ∀ τ : M →+* ℂ, (CG.mk π').infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E M))
  weak : ∀ (l' : ℕ) [Fact l'.Prime] (ι : Qbar l' ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l')), Weak π ι r → Weak π' ι (GlobalTheory.AboveL.resTo M r)

end GlobalTheory.Cong

end
