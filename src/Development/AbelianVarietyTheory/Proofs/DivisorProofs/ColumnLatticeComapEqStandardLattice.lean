module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
namespace GlobalTheory.ColStd

theorem sum_smul_col {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) (c : Fin n → 𝓞 K) :
    (∑ j, c j • (fun a => (B : Matrix (Fin n) (Fin n) K) a j)) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => algebraMap (𝓞 K) K (c j)) := by
  ext a
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mulVec_inj {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) {x y : Fin n → K}
    (h : (B : Matrix (Fin n) (Fin n) K) *ᵥ x = (B : Matrix (Fin n) (Fin n) K) *ᵥ y) : x = y :=
  Matrix.mulVec_injective_iff_isUnit.2 B.isUnit h

theorem colLat_comap_eq_stdLat {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) :
    (Formalism.L2.DIV.colLat B).comap ((Matrix.mulVecLin B.1).restrictScalars (𝓞 K)) = Formalism.L2.Pj.stdLat K n := by
  ext v
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    Formalism.L2.DIV.colLat]
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hv
    rw [sum_smul_col] at hc
    have := mulVec_inj B hc
    intro i
    exact ⟨c i, congrFun this i⟩
  · intro hv
    choose w hw using hv
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).2 ⟨w, ?_⟩
    rw [sum_smul_col]
    congr 1
    funext j
    exact hw j

end GlobalTheory.ColStd
