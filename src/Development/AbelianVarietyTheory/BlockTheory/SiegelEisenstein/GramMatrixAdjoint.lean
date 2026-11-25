module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
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

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped TensorProduct NNReal Matrix ComplexConjugate

def blocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

variable (D : D7)

def skewJ (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E := blocks 0 1 (-1) 0

abbrev UA {k : ℕ} (T : Matrix (Fin k) (Fin k) D.host.E) : Type := AdelicU.GAd D.sp.cm.sig T

abbrev GG (n : ℕ) : Type := UA D (skewJ D n)

variable {D}

def mat {k : ℕ} {T : Matrix (Fin k) (Fin k) D.host.E} (g : UA D T) : Matrix (Fin k) (Fin k) (AE D) :=
  (AdelicU.matHom (AF D.host.F) D.sp.cm.sig T g).1

def mmul {k l r : ℕ} (x : Mx D k l) (y : Mx D l r) : Mx D k r := HMul.hMul x y

def adj {k l : ℕ} (x : Mx D k l) : Mx D l k := Formalism.UG.cT (cA D) x

variable (D)

variable {D}

section Space

variable {m n : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E)

def wittIdx : ℕ :=
  sSup {r | ∃ W : Submodule D.host.E (Fin m → D.host.E),
    (∀ x ∈ W, ∀ y ∈ W, hE D.sp.cm.sig T x y = 0) ∧ Module.finrank D.host.E W = r}

def gramQ (x y : Mx D m n) : Mx D n n :=
  mmul (mmul (adj x) (T.map (incA D))) y

def trA (z : AE D) : AF D.host.F := Algebra.trace (AF D.host.F) (AE D) z

def pairing (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) : ℂ := ψ (trA (Matrix.trace (gramQ T x y)))

end Space

abbrev Sch (θ : InfFam D) (m n : ℕ) : Type := ModerateGrowthSchwartz.schwartzA θ m n

abbrev Rep (θ : InfFam D) (n : ℕ) {m : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E) : Type :=
  GG D n × UA D T →* Module.End ℂ (Sch θ m n)

section Weil

variable {θ : InfFam D} {m n : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E}



def s0 (m n : ℕ) : ℂ := (m : ℂ) / 2 - (n : ℂ) / 2

end Weil

end GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

end
