module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem bilinPart_eigen_mem_range : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (a : O) (u u' : Fin d → R) (α α' : R), (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k α • (fun i => algebraMap R k (u i)) → (dAct k B (star a)).mulVec (fun i => algebraMap R k (u' i)) = algebraMap R k α' • (fun i => algebraMap R k (u' i)) → IsUnit (α - α') → dotProduct (fun i => algebraMap R k (u i)) ((bilinPart k h).mulVec (fun i => algebraMap R k (u' i))) ∈ (algebraMap R k).range := by
  intro R _ d O _ _ k _ _ _ B h hc a u u' α α' hu hu' hα
  choose M hM using fun i j => WickVanishing.M_int B h hc a i j
  set v : Fin d → k := fun i => algebraMap R k (u i) with hv
  set v' : Fin d → k := fun i => algebraMap R k (u' i) with hv'
  have hS : sg1 k h = -(bilinPart k h).transpose := by
    ext i j
    simp only [WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, Matrix.neg_apply, Matrix.transpose_apply, bilinPart]
  have e1 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      -(algebraMap R k (α - α') * dotProduct v ((bilinPart k h).mulVec v')) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, dotProduct_sub,
      Matrix.dotProduct_mulVec v' (dAct k B (star a)).transpose, Matrix.vecMul_transpose, hu', Matrix.mulVec_smul,
      dotProduct_smul, smul_dotProduct, hS, Matrix.neg_mulVec, dotProduct_neg,
      Matrix.dotProduct_mulVec v', Matrix.vecMul_transpose, dotProduct_comm _ v, map_sub]
    simp only [smul_eq_mul]
    ring
  have e2 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      algebraMap R k (∑ i, u' i * ∑ j, M i j * u j) := by
      simp only [map_sum, map_mul, hM, dotProduct, Matrix.mulVec, hv, hv']
  obtain ⟨w, hw⟩ := hα.exists_left_inv
  refine ⟨-(w * ∑ i, u' i * ∑ j, M i j * u j), ?_⟩
  rw [map_neg, map_mul, ← e2, e1, mul_neg, neg_neg, ← mul_assoc, ← map_mul, hw, map_one, one_mul]

end GlobalTheory
