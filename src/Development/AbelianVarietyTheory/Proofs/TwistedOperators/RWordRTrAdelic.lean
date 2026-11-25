module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom

namespace GlobalTheory.Size

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem adAt_mem_lieAt (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : adAt θ k τ X ∈ lieAt V τ := by

  have hU : Matrix.conjTranspose (infMat D.sp.cm.sig V.gram (θ τ) k) * gramAt D V τ *
      infMat D.sp.cm.sig V.gram (θ τ) k = gramAt D V τ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  exact skew_conj hU (GlobalTheory.Mem.AutSpace.infMat_mul_inv (θ := θ) (V := V) (τ := τ) (g := k)) hX

private theorem infMat_eq_one_of_mem_GfC {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) f = 1 := by

  have h1 : infHom V f = 1 := hf
  have h2 := congrArg (fun u => (u.val).map (θ τ)) h1
  simp only [Units.val_one] at h2
  rw [Matrix.map_one (θ τ) (map_zero (θ τ)) (map_one (θ τ))] at h2
  exact h2

private theorem adAt_mul_of_mem_GfC (a : GA D V) {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : adAt θ (a * f) τ X = adAt θ a τ X := by

  unfold adAt
  rw [mul_inv_rev, GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_eq_one_of_mem_GfC hf τ,
    infMat_eq_one_of_mem_GfC (inv_mem hf) τ, one_mul, mul_one]

theorem oneP_mul_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : oneP θ V τ X t * k = k * oneP θ V τ (adAt θ k τ X) t := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have hreal : IsRealPt θ a := ⟨ha, fun σ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a σ⟩
  have hinf : oneP θ V τ (adAt θ a τ X) t ∈ GinfC V := atTau_mem V τ _
  rw [adAt_mul_of_mem_GfC a hf, ← mul_assoc, oneP_mul hθ hreal hX t, mul_assoc, mul_assoc,
    comm_of_mem V hinf hf]

theorem Rder_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ (adAt θ k τ X) φ) := by

  funext g
  show deriv (fun t : ℝ => φ (g * oneP θ V τ X t * k)) 0 = deriv (fun t : ℝ => φ (g * k * oneP θ V τ (adAt θ k τ X) t)) 0
  congr 1
  funext t
  rw [mul_assoc, oneP_mul_adelic hθ k hX t, ← mul_assoc]

theorem rTr_mem_smFun (hθ : IsInfFam θ) (k : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    rTr V k φ ∈ SmFun θ V := by

  intro n τs Xs hXs g
  have key := hφ n τs (fun i => adAt θ k (τs i) (Xs i)) (fun i => adAt_mem_lieAt hθ k (hXs i)) (g * k)
  convert key using 1
  funext t
  show φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * k) =
    φ (g * k * (List.ofFn fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)).prod)
  rw [mul_assoc, prod_mul_eq k n (fun i => oneP θ V (τs i) (Xs i) (t i))
    (fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)) (fun i => oneP_mul_adelic hθ k (hXs i) (t i)),
    ← mul_assoc]

end GlobalTheory.Size

end
