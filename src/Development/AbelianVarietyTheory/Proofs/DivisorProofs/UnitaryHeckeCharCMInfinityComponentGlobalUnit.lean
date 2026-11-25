module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem inf_mu_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ v : InfinitePlace E, (v.embedding (k : E) / (‖v.embedding (k : E)‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ e hμ k
  have h1 : μ.inf k = chiInf μ (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)) := by
    rw [chiInf, MonoidHom.comp_apply, GlobalTheory.CuspRep.NormTriv.infId_pInf]
    change μ.1 (Formalism.L2.Host.infDiag k) = _
    rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply]
    rfl
  rw [h1, hμ.2.2.2.2]
  refine Finset.prod_congr rfl fun v _ => ?_
  have : (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)).1 v = v.embedding (k : E) :=
    GlobalTheory.CuspRep.pInf_algebraMap (k : E) v
  rw [this]

end GlobalTheory.BCT
