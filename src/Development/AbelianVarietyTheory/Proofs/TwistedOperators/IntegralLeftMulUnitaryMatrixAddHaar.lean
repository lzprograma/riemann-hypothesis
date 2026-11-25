module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHermNDInvTranspose
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryGramAdelicMatrixHaarEq
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

noncomputable section

namespace GlobalTheory.Twist.LeftHaar

def transposeCAE (D : D7) (m n : ℕ) : Mx D m n ≃ₜ+ Mx D n m where
  toAddEquiv := Matrix.transposeAddEquiv (Fin m) (Fin n) (AE D)
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem map_left_unitary (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r))
    (hν : ν.IsAddHaarMeasure) :
    ν.map (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) = ν := by
  first | exact _root_.GlobalTheory.map_mt_mul_eq | exact @_root_.GlobalTheory.map_mt_mul_eq | apply _root_.GlobalTheory.map_mt_mul_eq <;> assumption

theorem integral_left_unitary : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)),
    ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ,
    ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν =
      ∫ y, Φ y ∂ν := by
  intro D W r h ν hν Φ
  let u := HA.mat (AF D.host.F) D.sp.cm.sig W.gram h
  have hmt : mt W h = u.1 := rfl
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  let e : Mx D W.rank r ≃ᵐ Mx D W.rank r :=
    { toFun := fun y => (HMul.hMul u.1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      invFun := fun y => (HMul.hMul (u⁻¹).1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      left_inv := fun y => by
        show (u⁻¹).1 * (u.1 * y) = y
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        show u.1 * ((u⁻¹).1 * y) = y
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      measurable_toFun := (continuous_const.matrix_mul continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mul continuous_id).measurable }
  have hmap := map_left_unitary D W r h ν hν
  rw [hmt] at hmap
  have he : Measure.map (⇑e) ν = ν := hmap
  have := integral_map_equiv (μ := ν) e Φ
  rw [he] at this
  rw [hmt]
  exact this.symm

end GlobalTheory.Twist.LeftHaar

end
