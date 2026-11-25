module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kerPD (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) :
    Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :=
  Submodule.span ℂ {Φ₀D | Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
    ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0}

theorem mem_kerPD {ψ : AddChar (AF D.host.F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (θ : InfFam D) {W W₁ X : HSp D}
    (A₁ : Fr W₁) (B : Fr X) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) (Φ₀D : (Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :
    Φ₀D ∈ kerPD ψ θ A₁ B Bs Γ cB p' ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
      ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  have hl := isDatum_linear Γ.M' ψ hψ (⇑cB)
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, hl.1, map_zero p'⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    obtain ⟨hy1, Φy, hΦy, hDy, hpy⟩ := hy
    refine ⟨Submodule.add_mem _ hx1 hy1, Φx + Φy, Submodule.add_mem _ hΦx hΦy, ?_, by rw [map_add (f := _), hpx, hpy, add_zero]⟩
    have := hl.2 x y Φx Φy 1 hDx hDy
    simpa using this
  | smul c x _ hx =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    refine ⟨Submodule.smul_mem _ c hx1, c • Φx, Submodule.smul_mem _ c hΦx, ?_, by rw [map_smul, hpx, smul_zero]⟩
    have := hl.2 0 x 0 Φx c hl.1 hDx
    simpa using this

end GlobalTheory.SquareAgree

end
