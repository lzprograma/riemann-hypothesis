module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Classical

namespace GlobalTheory.TraceFrames

theorem hO_eq_trace_mul {D : D7} (S T : HSp D) (k y : WO S T) :
    hO S T y k = Matrix.trace (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D))
      * (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]; enter [2, c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]




theorem toEAf_hO_eq_trace_frames {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D))
    (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) := by
  set X₀ : Matrix (Fin S.rank) (Fin T.rank) (AE D) := HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D)) with hX
  set Y₀ : Matrix (Fin T.rank) (Fin S.rank) (AE D) := y with hY
  set A : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := (βS⁻¹).val with hA
  set A' : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := βS.val with hA'
  set B : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := βT.val with hB
  set B' : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := (βT⁻¹).val with hB'
  set Xf : Matrix (Fin S.rank) (Fin T.rank) (Datum.EAf D) := X₀.map (toEAf D) with hXf
  set Yf : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := Y₀.map (toEAf D) with hYf
  have hBB : HMul.hMul B B' = (1 : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D)) := Units.mul_inv βT
  have hAA : HMul.hMul A' A = (1 : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) := Units.mul_inv βS
  have h1 : frMapAdj S T βS βT k = HMul.hMul (HMul.hMul A Xf) B := rfl
  have h2 : frMapO S T βS βT y = HMul.hMul (HMul.hMul B' Yf) A' := rfl
  have h4 : HMul.hMul Xf Yf = (HMul.hMul X₀ Y₀ : Matrix (Fin S.rank) (Fin S.rank) (AE D)).map (toEAf D) :=
    (Matrix.map_mul).symm
  have h3 : (HMul.hMul (HMul.hMul (HMul.hMul A Xf) B) (HMul.hMul (HMul.hMul B' Yf) A') :
      Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) = HMul.hMul A (HMul.hMul (HMul.hMul Xf Yf) A') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
  rw [h1, h2, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, hAA, Matrix.mul_one, h4, hO_eq_trace_mul]

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rfl

end GlobalTheory.TraceFrames
