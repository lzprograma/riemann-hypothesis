module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.FrameMove

open Formalism.UG (bc cT)

theorem conj_gram {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (β G h : GL (Fin n) A) (hG : G.val = cT σ β.val * J * β.val)
    (hx : β * h * β⁻¹ ∈ Formalism.UG.UJ σ J) :
    (G * h * G⁻¹).val = cT σ (h⁻¹).val := by
  have hx' : cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val = J := hx
  have e1 : cT σ h.val * G.val * h.val = G.val := by
    have e : (β * h * β⁻¹).val * β.val = β.val * h.val := by
      rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
    calc cT σ h.val * G.val * h.val = cT σ (β.val * h.val) * J * (β.val * h.val) := by
          rw [hG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ β.val * (cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val) * β.val := by
          rw [← e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G.val := by rw [hx', hG]
  have e2 : cT σ (h⁻¹).val * cT σ h.val = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc (G * h * G⁻¹).val = (cT σ (h⁻¹).val * cT σ h.val) * (G.val * h.val * (G⁻¹).val) := by
        rw [e2, Matrix.one_mul]; rfl
    _ = cT σ (h⁻¹).val * ((cT σ h.val * G.val * h.val) * (G⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = cT σ (h⁻¹).val := by rw [e1, Units.mul_inv, Matrix.mul_one]

theorem conj_gram_sub {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (O : Subring A) (J : Matrix (Fin n) (Fin n) A)
    (β : GL (Fin n) A) (G h : GL (Fin n) O) (hG : (bc O.subtype G).val = cT σ β.val * J * β.val)
    (hx : β * bc O.subtype h * β⁻¹ ∈ Formalism.UG.UJ σ J) (i j : Fin n) :
    (((G * h * G⁻¹).val i j : O) : A) = σ ((h⁻¹).val j i : O) := by
  have c := conj_gram σ J β (bc O.subtype G) (bc O.subtype h) hG hx
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul] at c
  exact congrFun (congrFun c i) j

end GlobalTheory.FrameMove
