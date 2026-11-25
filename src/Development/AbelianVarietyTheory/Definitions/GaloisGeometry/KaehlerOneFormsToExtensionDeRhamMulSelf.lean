module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Trace.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair

@[expose] public section

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD

namespace GlobalTheory.W1

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

def map1 : Ω[K⁄k] →ₗ[K] DR k L :=
  ((ι1 (R := k) (B := L)).restrictScalars K).comp (KaehlerDifferential.map k k K L)

open KaehlerDifferential in
variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] in
theorem _root_.GlobalTheory.W1.kaehlerOneFormsToExtensionDeRham_mul_self (ω : Ω[K⁄k]) :
    _root_.GlobalTheory.W1.map1 k K L ω * _root_.GlobalTheory.W1.map1 k K L ω = 0 := by
  unfold _root_.GlobalTheory.W1.map1 _root_.GlobalTheory.CechDR.ι1
  exact ExteriorAlgebra.ι_sq_zero _

def mapDR : DR k K →ₐ[K] DR k L := ExteriorAlgebra.lift K ⟨map1 k K L, kaehlerOneFormsToExtensionDeRham_mul_self k K L⟩

def IsTrDR (T : DR k L →ₗ[k] DR k K) : Prop :=
  ∀ (b : L) (ω : DR k K), T (b • mapDR k K L ω) = Algebra.trace K L b • ω


open scoped Classical in
open Classical in
def trDR : DR k L →ₗ[k] DR k K := if h : ∃ T, IsTrDR k K L T then h.choose else 0

variable {k K L} {ι : Type}

def trC (c : Finset ι → DR k L) : Finset ι → DR k K := fun s => trDR k K L (c s)

end GlobalTheory.W1
