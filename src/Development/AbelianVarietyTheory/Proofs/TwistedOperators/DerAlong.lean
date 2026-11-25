module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal TensorProduct

namespace GlobalTheory.MixedTerm

variable {D : D7}

def term (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E) : ℂ :=
  res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G) 0

def phase (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) : ℂ :=
  ψ (symplO V W (isoPart V W C' (Matrix.map y (incA D))) (isoPart V W C κ))

def pairQ (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin W.rank) D.host.E :=
  D.host.xi0 • (adj D y * W.gram)

def ratPair (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) : ℝ :=
  ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * x)) : ℚ) : ℝ)

def dirAt (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin r) ℂ) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  z * (adj D C * V.gram).map (tauE D τ)

def derAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  ∑ τ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G

def finLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 0 1 : AF D.host.F) ⊗ₜ[D.host.F] e

end GlobalTheory.MixedTerm

end
