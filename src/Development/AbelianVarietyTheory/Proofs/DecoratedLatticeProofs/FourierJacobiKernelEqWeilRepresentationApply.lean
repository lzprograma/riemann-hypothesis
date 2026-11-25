module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem fjKer_eq_om_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  intro D ψ W W₀ V₀ A L ρ dW o ζ χ χ' om hW Ξ hΞ h₀ n h
  have hp : (o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n) = ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    rw [← ptT_yZero_vecB o dW ζ n, AddEquiv.symm_apply_apply]
  have hfix : actO V₀ W₀ (o.emb (h₀, 1)) 1 (ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n) =
      ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    apply (o.resS W₀).injective
    rw [o.resS_actO, ptT_yZero_vecB]
    simp only [actO_eq, inv_one, mt_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul]
  have hm : om (o.emb (h₀, 1), 1) (om (1, h) Ξ) = om (o.emb (h₀, 1), h) Ξ := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [hp, fjKer, opA, jacT, map_smul, hW.om_heis _ _ _ _ (hW.om_pres _ _ hΞ), hfix, hm, cenT_yZero_vecB]
  simp only [Pi.smul_apply, smul_eq_mul, heisO, zero_add, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Unf
