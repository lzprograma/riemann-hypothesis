module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaFinsetSumSmulOfXiExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms

@[expose] public section

noncomputable section

namespace GlobalTheory.GivenXi

open scoped Matrix.Norms.Elementwise

section sesq

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.JCx4
open scoped ComplexConjugate

theorem formLev_sesquilinear (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) (hmm : P5.mmUser P0 w.length ≤ mm)
    (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : ∀ a, InCC A mm (x a)) (hx' : ∀ a, InCC A mm (x' a)) (hy : ∀ a, InCC A mm (y a)) :
    D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
      D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x' := by
  exact _root_.Formalism.FourierDecayAlt.P.JCx4.formLev_sesq_core P0 T s j w A mm hA hmm x x' y c hx hx' hy

theorem formLev_norm_le (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (u v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu cv : ℝ),
      (∀ b, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u b) cu) →
      (∀ a, CCle (A - 1 - 2 * (w.length : ℝ)) 5 (v a) cv) →
      ‖D.formLev T s j w u v‖ ≤ Cf * cu * cv := by
  let _ := hΞ
  exact formLev_bound_mm P0 T s j w A hA

theorem formLev_sesquilinear_finiteReg (hΞ : B.XiExists) : Formalism.FourierDecayAlt.JC.FormLevSesqMM := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε _ hA hmm x x' y c hx hx' hy
  exact formLev_sesquilinear hΞ P0 T s j w A mm hA hmm x x' y c (fun a => (hx a).2.1) (fun a => (hx' a).2.1)
    (fun a => (hy a).2.1)

end sesq

section limit

open Matrix MeasureTheory Filter Topology
open scoped ContDiff
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBE Formalism.FourierDecayAlt.P.JCTx6.Lev0

theorem formLev_tendsto (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ℕ → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ℕ → ℝ)
    (hdn : Tendsto dn atTop (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hxn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e) Bd)
    (hyn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd)
    (hdx : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n))
    (hdy : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n)) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) atTop (𝓝 (D.formLev T s j w x y)) := by
  let _ := hΞ
  exact formLev_limit P0 T s j w N hw ε₀ hε₀ x y xn yn Bd dn hdn hx hy hxn hyn hdx hdy

theorem levelForm_cutoff_tendsto_below (hΞ : B.XiExists) : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ Cc : ℝ, Cl ≤ Cc →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ i, i ≤ P.r → ∀ w : List C.Letter, w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b)) := by
  exact _root_.Formalism.FourierDecayAlt.P.PBE.belowTop

theorem levelForm_cutoff_tendsto (hΞ : B.XiExists) : Formalism.FourierDecayAlt.KB.FormLimit := by
  exact _root_.Formalism.FourierDecayAlt.P.limit_of_module_forms

end limit

end GlobalTheory.GivenXi

end
