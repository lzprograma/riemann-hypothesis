module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoStar :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v (x : Lsq (Kv v) (cv v P.Δ)) (a : Af L), (∀ w h, P.rho v w h x = pLoc L w a) → ∀ w h, P.rho v w h (star x) = pLoc L w (cjF a) := by
  intro L _ _ _ P v x a hx w h
  have hu : un (conjSrc (IsCMField.complexConj L).toRingEquiv w) = v := by
    rw [← h]; exact GlobalTheory.LocInj.under_conjSrc w
  have hφ : ∀ y : Kv v, conjLoc (IsCMField.complexConj L).toRingEquiv w
      (P.φ v _ hu y) = P.φ v w h y := by
    intro y
    refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (Lp L) v).equalizer
      ((conjLoc_spec _ w).1.comp (P.φ_cont v _ hu)) (P.φ_cont v w h) (funext fun b => ?_)) y
    simp only [Function.comp_apply]
    rw [P.φ_alg, P.φ_alg, (conjLoc_spec _ w).2.1]
    congr 1
    exact AlgEquiv.commutes (IsCMField.complexConj L) b
  have hrt : conjLoc (IsCMField.complexConj L).toRingEquiv w (P.rt (conjSrc (IsCMField.complexConj L).toRingEquiv w)) = - P.rt w := by
    rw [Pre.rt, (conjLoc_spec _ w).2.1, Pre.rt, ← map_neg, ← map_neg]
    congr 1
    have hs : star (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = - QuadraticAlgebra.omega := by
      ext <;> simp
    change IsCMField.complexConj L (P.e QuadraticAlgebra.omega) = _
    rw [← P.e_star, hs]
  rw [cjF, pLoc_conjFin, ← hx _ hu]
  change P.φ v w h (star x).re + P.φ v w h (star x).im * P.rt w =
    conjLoc (IsCMField.complexConj L).toRingEquiv w (P.φ v _ hu x.re + P.φ v _ hu x.im * P.rt _)
  rw [map_add (f := _), map_mul, hφ, hφ, hrt]
  simp
