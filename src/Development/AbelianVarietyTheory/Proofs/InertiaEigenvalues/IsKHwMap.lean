module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
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

open Formalism.BasicNotions Formalism.IndefR.Links

namespace GlobalTheory.LowestKType

variable {D : D7} {n m : ℕ}

def kop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def sop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def Cpt (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Prop :=
  ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ)

def IsHarm (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  ∀ (τ : D.what₂.Tau) (i l : Fin m), w.p τ ≤ (i : ℕ) → (l : ℕ) < w.p τ → kop w τ i l P = 0

def IsKHw (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a P = c • P

def IsKHwMap {W : Type} [AddCommGroup W] [Module ℂ W] (w : GlobalTheory.ExportSeries.Weight D n)
    (ψ : W →ₗ[ℂ] PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b ∘ₗ ψ = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a ∘ₗ ψ = c • ψ

def IsNHw (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin n), a < b → sop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin n), sop w τ a a P = lam τ a • P

end GlobalTheory.LowestKType

end
