module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical

namespace GlobalTheory.Fam.Inhab

open GlobalTheory.SymBridge

section Frames

variable {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

def stdFr (k : Type) [Field k] (e : Y ≃ Fin N) : GlobalTheory.LocMod.Frame k N Y where
  β := (1 : Matrix (Fin N) (Fin N) k).submatrix id e
  γ := (1 : Matrix (Fin N) (Fin N) k).submatrix e id
  βγ := by rw [Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]
  γβ := by
    have h := Matrix.submatrix_mul_equiv (1 : Matrix (Fin N) (Fin N) k) (1 : Matrix (Fin N) (Fin N) k) e (Equiv.refl _) e
    rw [Matrix.one_mul, Matrix.submatrix_one_equiv] at h
    exact h

theorem isStdFr_stdFr {pos : Y → ℕ} {e : Y ≃ Fin N} (h : IsOrd pos e) : IsStdFr pos (stdFr k e) := ⟨e, h, rfl⟩

def blockOrd (κ τ l j : ℕ) : (Fin κ ⊕ Fin l) ⊕ Fin j × Fin τ ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem isOrd_xPos (κ τ j : ℕ) : IsOrd (xPos (κ := κ) (τ := τ) (j := j)) (blockOrd κ τ j j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, xPos, finProdFinEquiv]
  ring

theorem isOrd_zPos (κ τ l j : ℕ) : IsOrd (zPos (κ := κ) (τ := τ) (l := l) (j := j)) (blockOrd κ τ l j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, zPos, finProdFinEquiv]
  ring

end Frames

end GlobalTheory.Fam.Inhab

end
