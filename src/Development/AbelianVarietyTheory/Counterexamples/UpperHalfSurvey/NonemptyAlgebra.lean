module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import ReciprocityTheory.DualLattices.CyclicRecursionStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import ReciprocityTheory.DualLattices.DvdOfCoeffZero
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
public import ReciprocityTheory.DualLattices.MulIterateRootEqZero
public import ReciprocityTheory.DualLattices.ValUntiltESubOne
public import ReciprocityTheory.DualLattices.ZmodTrichotomy

@[expose] public section

open WittVector Ideal ReciprocityTheory.PGsh

namespace GlobalTheory.AinfChecks


open WittVector Ideal in
theorem _root_.GlobalTheory.AinfChecks.padicComplex (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]),
      (∃ pflat : PreTilt 𝓞_ℂ_[p] p, pflat.untilt = ((p : ℕ) : 𝓞_ℂ_[p])) ∧
      (∃ ε : PreTilt 𝓞_ℂ_[p] p,
        IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p) ∧
      _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.XiNuStatement p ℂ_[p] Valued.v 𝓞_ℂ_[p] ∧
      _root_.ReciprocityTheory.PGsh.RegularStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.FlatW'Statement p 𝓞_ℂ_[p] := by
  obtain ⟨hunit, hcomp, ε, hv, hε⟩ := _root_.GlobalTheory.PadicComplexHost.main p
  have hker : _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] := _root_.ReciprocityTheory.PGsh.kerTheta ℂ_[p] Valued.v hv
  refine ⟨hunit, hcomp, _root_.ReciprocityTheory.PGsh.exists_pflat ℂ_[p] Valued.v 𝓞_ℂ_[p] hv, ⟨ε, hε⟩, hker,
    _root_.ReciprocityTheory.PGsh.xiNu p ℂ_[p] Valued.v 𝓞_ℂ_[p] hker, ?_, _root_.ReciprocityTheory.PGsh.flatW' p 𝓞_ℂ_[p]⟩
  refine _root_.ReciprocityTheory.PGsh.regular p 𝓞_ℂ_[p] fun x hx => ?_
  have h : ((p : ℂ_[p]) * (x : ℂ_[p])) = 0 := by
    simpa using congrArg (fun y : 𝓞_ℂ_[p] => (y : ℂ_[p])) hx
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  · exact Subtype.ext h

end GlobalTheory.AinfChecks
