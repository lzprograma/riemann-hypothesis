module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain

def GoodAll {R : Ranks} {H : Formalism.BasicNotions.Host R} {a : ℕ} (π : HostCGu H a) : Prop :=
  haveI := host_isCMField H
  ∀ w : HeightOneSpectrum (𝓞 H.E), UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.1.loc w)⟩ : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion H.E))

structure CGTrueT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) where
  e : ∀ a, D.naut.CG a ↪ HostCGu D.host a
  good : ∀ a (π : D.naut.CG a), GoodAll (e a π)
  surj : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, e a π = ρ
  zero : IsEmpty (D.naut.CG 0)
  loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLawsT.locGT hT D.nd.plOm (e a π) w
  tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ)
  inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ
  csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd

end GlobalTheory.HeightCounting

end
