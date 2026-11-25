module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

namespace Place

def intInd (Y Y' : Type) : Matrix Y Y' k → ℂ := Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1

def tensorAt (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) : WO S T → ℂ :=
  fun t => Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)

def tensorL (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := p.tensorAt FS FT Φ Ψ.1
  map_add' Ψ Ψ' := by
    funext t
    simp only [tensorAt, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c Ψ := by
    funext t
    simp only [tensorAt, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorL_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : SB (Matrix Y Y' k)) :
    p.tensorL FS FT Φ Ψ = p.tensorAt FS FT Φ Ψ.1 := rfl

def tensorOne (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ (intInd Y Y')
  map_add' Φ Φ' := by
    funext t
    simp only [tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorOne_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    p.tensorOne FS FT Φ = p.tensorAt FS FT Φ (intInd Y Y') := rfl

end Place
end GlobalTheory.LocMod
end
