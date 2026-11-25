module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar

namespace GlobalTheory.AdelicScalar

theorem conjFrame_mem_UH : ∀ (p q n : ℕ), p + q = n → ∀ (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), (Aᴴ * Formalism.UG.Jpq p q * A : Matrix (Fin n) (Fin n) ℂ) = Gm → IsUnit Gm.det → ∀ b : UpqT p q, conjFrame Gm A (UpqT.mat b) ∈ Formalism.QuantumDeterminants.UH Gm := by
  intro p q n hn Gm A hA hG b
  have h1 : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ hG
  have hb : (UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b = Formalism.UG.Jpq p q := b.2
  have hl : (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have e : Fin n ≃ Fin p ⊕ Fin q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hr : A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  have hc : A * conjFrame Gm A (UpqT.mat b) = UpqT.mat b * A := by
    have : A * conjFrame Gm A (UpqT.mat b) = A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * (UpqT.mat b * A) := by
      simp only [conjFrame, Matrix.mul_assoc]
    rw [this, hr, Matrix.one_mul]
  change (conjFrame Gm A (UpqT.mat b))ᴴ * Gm * conjFrame Gm A (UpqT.mat b) = Gm
  generalize conjFrame Gm A (UpqT.mat b) = C at hc
  calc Cᴴ * Gm * C = (A * C)ᴴ * Formalism.UG.Jpq p q * (A * C) := by
        rw [← hA]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * ((UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b) * A := by
        rw [hc]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gm := by rw [hb, hA]

end GlobalTheory.AdelicScalar
