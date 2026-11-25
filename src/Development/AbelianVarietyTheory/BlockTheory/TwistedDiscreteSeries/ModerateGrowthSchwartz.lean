module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory GlobalTheory.Doubling
open scoped TensorProduct ENNReal NNReal ComplexConjugate

variable {D : D7}

def schwartzA (θ : InfFam D) (m n : ℕ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))}

variable (A B : HSp D)

def cols (x y : WO A B) : WO (dblSp A) B := (Matrix.fromCols x y).submatrix id finSumFinEquiv.symm

def fstCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inl j)

def sndCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inr j)

def half (D : D7) : AE D := incA D (1 / 2)

def onX (x : WO A B) : WO (dblSp A) B := cols A B (half D • x) (half D • x)

def onY (y : WO A B) : WO (dblSp A) B := cols A B y (-y)

def xOf (w : WO (dblSp A) B) : WO A B := fstCols A B w + sndCols A B w

def yOf (w : WO (dblSp A) B) : WO A B := half D • (fstCols A B w - sndCols A B w)

variable {A B}

def thetaInt (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (f₁ f₂ : WO A B → ℂ) (g₁ g₂ : GA D A) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ‖thetaKO om g₁ h f₁ * thetaKO om g₂ h f₂‖ₑ ∂μ

abbrev ht (V : HSp D) (g : GA D V) : ℝ≥0 := AdelicU.height D.sp.cm.sig V.gram g

variable (A B)

def InRange : Prop := 1 ≤ A.rank ∧ A.rank < B.rank ∧ (Cusp.wittIndex B = 0 ∨ A.rank + Cusp.wittIndex B < B.rank)

theorem half_add_half : half D + half D = 1 := by
  rw [half, ← map_add (f := _), add_halves, map_one]

theorem fstCols_cols (x y : WO A B) : fstCols A B (cols A B x y) = x := by
  ext i j; simp [fstCols, cols]

theorem sndCols_cols (x y : WO A B) : sndCols A B (cols A B x y) = y := by
  ext i j; simp only [sndCols, cols, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem coords (x y : WO A B) : xOf A B (onX A B x) = x ∧ yOf A B (onX A B x) = 0 ∧
    xOf A B (onY A B y) = 0 ∧ yOf A B (onY A B y) = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [xOf, yOf, onX, onY, fstCols_cols, sndCols_cols]
  · rw [← add_smul, half_add_half, one_smul]
  · simp
  · simp
  · rw [sub_neg_eq_add, smul_add, ← add_smul, half_add_half, one_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

end
