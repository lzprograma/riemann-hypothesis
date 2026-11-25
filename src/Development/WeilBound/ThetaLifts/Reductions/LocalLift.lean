module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.WeilBound.ThetaLifts.Reductions.MetaDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import CompanionTheory.ThickeningEstimates.LieGroupReduction.IsoOfIntegral
import Development.WeilBound.ThetaLifts.CartanFactorisation.EqOfInner
import CompanionTheory.ThickeningEstimates.LieGroupReduction.HasDerivAtSchwartzToL2
import CompanionTheory.ThickeningEstimates.LieGroupReduction.NormExpSubLe
import CompanionTheory.ThickeningEstimates.LieGroupReduction.LocalLift
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.ThetaLifts.Reductions.IsoOfIntegral, Development.WeilBound.ThetaLifts.Reductions.HasDerivAtSchwartzToL2, Development.WeilBound.ThetaLifts.Reductions.LocalLift

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.IsoOfIntegral =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.IsoOfIntegral", "h": "module\n\nimport CompanionTheory.ThickeningEstimates.LieGroupReduction.IsoOfIntegral\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.WeilBound.ThetaLifts.CartanFactorisation.EqOfInner\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKR.LL

variable {l : Type} [Fintype l]

abbrev Eu (l : Type) : Type := EuclideanSpace ℝ l

def rf (p q : Eu l) (f : Eu l → ℂ) : Eu l → ℂ :=
  fun x => exp (((2 * π * ⟪q, x⟫ + π * ⟪p, q⟫ : ℝ) : ℂ) * I) * f (x + p)

def Intw (S : Sch l →L[ℂ] Sch l) (p q p' q' : Eu l) : Prop :=
  ∀ f g : Sch l, ⇑g = rf p q f → ⇑(S g) = rf p' q' (S f)

def Iso (S : Sch l →L[ℂ] Sch l) : Prop := ∀ f, ‖schwartzToL2 l (S f)‖ = ‖schwartzToL2 l f‖

theorem Intw.smul {S : Sch l →L[ℂ] Sch l} {p q p' q' : Eu l} (hS : Intw S p q p' q') (c : ℂ) :
    Intw (c • S) p q p' q' :=
  _root_.CompanionTheory.ThKR.LL.Intw.smul hS c

theorem Iso.mul {S T : Sch l →L[ℂ] Sch l} (hS : Iso S) (hT : Iso T) : Iso (S * T) := fun f => (hS _).trans (hT f)

def ph (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I)


open Classical in
def dil (B : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  if h : IsUnit B then compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.ofUnit h.unit) else 0

def fou (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierCLM ℂ (Sch l)

def fouInv (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierInvCLM ℂ (Sch l)

def big (Ai B C : Eu l →L[ℝ] Eu l) (c : ℝ) : Sch l →L[ℂ] Sch l :=
  ph (C * Ai) * (((c : ℂ) • dil Ai) * (fou l * (ph (-(Ai * B)) * fouInv l)))

end PositivityTheory.ThKR.LL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.IsoOfIntegral =====

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.HasDerivAtSchwartzToL2 =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.HasDerivAtSchwartzToL2", "h": "module\n\nimport CompanionTheory.ThickeningEstimates.LieGroupReduction.HasDerivAtSchwartzToL2\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Calculus.Deriv.Prod\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Monotonicity.Lemmas\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Presheaf\nimport Development.WeilBound.ThetaLifts.CartanFactorisation.EqOfInner\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real

namespace PositivityTheory.ThKR.LL

variable {l : Type} [Fintype l]

def LD (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l → Sch l) (t₀ : ℝ) : Prop :=
  ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) t₀

variable [DecidableEq l]

theorem weyl_step {V : Sch l →L[ℂ] Sch l} {w v : l ⊕ l → ℝ} (h : ∀ f, dRho w (V f) = V (dRho v f))
    (A : Sch l →L[ℂ] Sch l) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (V f)) = ∑ a, v a • schwartzToL2 l (A (V (dRho (Pi.single a 1) f))) := by
  rw [ContinuousLinearMap.mul_apply, h, dRho_eq_sum v]

  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  simp only [CompanionTheory.ThKR.LL.csmul]

theorem LD.differentiableAt {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l → Sch l} {t₀ : ℝ} (hV : LD V Q t₀)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv : ∀ w a, DifferentiableAt ℝ (fun t => v t w a) t₀)
    (h : ∀ᶠ t in 𝓝 t₀, ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    DifferentiableAt ℝ (fun t => lam (V t f)) t₀ := by
  have key : ∀ A ∈ weylAlg l, ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀ := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀)
      (fun f => (hV f).differentiableAt) ?_ (fun f => by simp) ?_ ?_ hA
    · intro A w ih f
      refine (DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_of_eventuallyEq ?_
      filter_upwards [h] with t ht
      exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).differentiableAt.comp t₀ (differentiableAt_pi.2 fun i => key _ (hA i) f)

theorem LD.hasDerivAt {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l →L[ℂ] Sch l} (hV : LD V Q 0) (h0 : ∀ f, V 0 f = f)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (v' : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv0 : ∀ w, v 0 w = w)
    (hv : ∀ w a, HasDerivAt (fun t => v t w a) (-v' w a) 0) (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (v' w))
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    HasDerivAt (fun t => lam (V t f)) (lam (Q f)) 0 := by
  have key : ∀ A ∈ weylAlg l, ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0 := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0)
      hV ?_ (fun f => by simpa using hasDerivAt_const _ _) ?_ ?_ hA
    · intro A w ih f
      refine ((HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_deriv ?_).congr_of_eventuallyEq ?_
      · have e : dRho w * Q = Q * dRho w - dRho (v' w) := by rw [← hQ, sub_sub_cancel]
        rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (dRho w), e, dRho_eq_sum w,
          dRho_eq_sum (v' w)]

        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul, hv0, h0,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub, neg_smul, ← sub_eq_add_neg,
        Finset.sum_sub_distrib]
        simp only [CompanionTheory.ThKR.LL.csmul]
      · filter_upwards [h] with t ht
        exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.2 fun i => key _ (hA i) f)

end PositivityTheory.ThKR.LL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.HasDerivAtSchwartzToL2 =====

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.LocalLift =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.LocalLift", "h": "module\n\nimport CompanionTheory.ThickeningEstimates.LieGroupReduction.LocalLift\npublic import Development.WeilBound.ThetaLifts.Reductions.MetaDef\npublic import Mathlib.Analysis.CStarAlgebra.Matrix\nimport Mathlib.Algebra.Order.Archimedean.Real.Hom\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\npublic import Mathlib.Analysis.Calculus.Deriv.Abs\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\npublic import Mathlib.Analysis.Normed.Algebra.MatrixExponential\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKR.LL

variable {l : Type} [Fintype l] [DecidableEq l]

def bl (i j : l → l ⊕ l) : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] (Eu l →L[ℝ] Eu l) where
  toFun g := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (g.submatrix i j)
  map_add' g h := by rw [← map_add (f := _)]; rfl
  map_smul' c g := by rw [RingHom.id_apply, ← map_smul]; rfl

theorem bl_apply (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (x : Eu l) (a : l) :
    bl i j g x a = ∑ b, g (i a) (j b) * x b := rfl

theorem sympl_exp {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (w w' : l ⊕ l → ℝ) :
    sympl (NormedSpace.exp X *ᵥ w) (NormedSpace.exp X *ᵥ w') = sympl w w' := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have hu : IsUnit (Matrix.J l ℝ) :=
    ⟨⟨Matrix.J l ℝ, -Matrix.J l ℝ, by rw [mul_neg, J_squared, neg_neg], by rw [neg_mul, J_squared, neg_neg]⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Xᵀ = Matrix.J l ℝ * -X * (Matrix.J l ℝ)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᵀ * (Matrix.J l ℝ * NormedSpace.exp X) = Matrix.J l ℝ := by
    have := CompanionTheory.ThKR.LL.exp_mul_exp_neg (-X)
    rw [neg_neg] at this
    rw [← Matrix.exp_transpose, h1, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.J l ℝ),
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_one]
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]

theorem differentiableAt_det {M : ℝ → Matrix l l ℝ} {t : ℝ} (h : ∀ i j, DifferentiableAt ℝ (fun t => M t i j) t) :
    DifferentiableAt ℝ (fun t => (M t).det) t := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun σ _ => (DifferentiableAt.fun_finsetProd fun i _ => h _ _).const_mul _

end PositivityTheory.ThKR.LL

namespace PositivityTheory.ThKR

open LL hiding big bl

open CompanionTheory.ThKR.LL (big big_one bl block_inl_inl_one block_inl_inr_one block_inr_inl_one det_bl
  exp_mul_exp_neg hasDerivAt_lin_exp intw_of_sympl isUnit_big iso_big ld_big quad_eq) in
theorem localLift_holds : LocalLift := by
  intro l _ _ X hX
  letI : HasSummableGeomSeries (Eu l →L[ℝ] Eu l) := by
      infer_instance
  let g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => NormedSpace.exp (t • X)
  have g0 : g 0 = 1 := by simp [g]
  have hd := fun i j t => hasDerivAt_lin_exp (bl i j) X t
  let A : ℝ → Eu l →L[ℝ] Eu l := fun t => bl Sum.inl Sum.inl (g t)
  let c : ℝ → ℝ := fun t => (√|(A t).det|)⁻¹
  let V : ℝ → Sch l →L[ℂ] Sch l := fun t =>
    big (Ring.inverse (A t)) (bl Sum.inl Sum.inr (g t)) (bl Sum.inr Sum.inl (g t)) (c t)
  have A0 : A 0 = 1 := by simp only [A, g0, block_inl_inl_one]
  have hopen : ∀ t, IsUnit (A t) → ∀ᶠ u in 𝓝 t, IsUnit (A u) := fun t ht =>
    (hd _ _ t).continuousAt.eventually (Units.isOpen.mem_nhds ht)
  have hdet : ∀ t, IsUnit (A t) → (Ring.inverse (A t)).det * (A t).det = 1 := fun t ht => by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ ht)
    simpa [ContinuousLinearMap.det] using this
  have hne : ∀ t, IsUnit (A t) → (A t).det ≠ 0 := fun t ht => right_ne_zero_of_mul_eq_one (hdet t ht)
  have hc : ∀ t, IsUnit (A t) → c t ^ 2 = |(Ring.inverse (A t)).det| := fun t ht => by
    rw [eq_inv_of_mul_eq_one_left (hdet t ht), abs_inv, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc0 : ∀ t, IsUnit (A t) → c t ≠ 0 := fun t ht =>
    inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 (hne t ht))).ne'
  have hcd : ∀ t, IsUnit (A t) → DifferentiableAt ℝ c t := fun t ht => by
    have h1 : DifferentiableAt ℝ (fun t => (A t).det) t := by
      simp only [A, det_bl]
      exact differentiableAt_det fun i j =>
        (hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ (Sum.inl i) (Sum.inl j)) X t).differentiableAt
    exact ((h1.abs (hne t ht)).sqrt (abs_pos.2 (hne t ht)).ne').inv (Real.sqrt_pos.2 (abs_pos.2 (hne t ht))).ne'
  have c0 : c 0 = 1 := by simp [c, A0, ContinuousLinearMap.det]
  have V0 : V 0 = 1 := by simp only [V, A0, g0, c0, block_inl_inr_one, block_inr_inl_one, Ring.inverse_one, big_one]
  have hU : ∀ t, IsUnit (A t) → IsUnit (V t) := fun t ht => isUnit_big ht.ringInverse _ _ (hc0 t ht)
  have hI : ∀ t, IsUnit (A t) → Impl (fun w => g t *ᵥ w) (V t).toLinearMap := fun t ht =>
    ⟨iso_big ht.ringInverse _ _ (hc t ht), fun w => intw_of_sympl (sympl_exp (SMulMemClass.smul_mem t hX)) ht _ w⟩
  let v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ) := fun t w => NormedSpace.exp (t • -X) *ᵥ w
  have hv : ∀ t w a, HasDerivAt (fun t => v t w a) (((NormedSpace.exp (t • -X) * -X) *ᵥ w) a) t := fun t w a =>
    hasDerivAt_lin_exp ((LinearMap.proj a).comp ((Matrix.mulVecBilin ℝ ℝ).flip w)) (-X) t
  have hw : ∀ t, IsUnit (A t) → ∀ w f, dRho w (V t f) = V t (dRho (v t w) f) := fun t ht w f => by
    have hs : Function.Surjective (V t).toLinearMap := fun f => ⟨Ring.inverse (V t) f, by
      show (V t * Ring.inverse (V t)) f = f
      rw [Ring.mul_inverse_cancel _ (hU t ht), ContinuousLinearMap.one_apply]⟩
    have := Impl.dRho (s := Matrix.mulVecLin (g t)) (hI t ht) hs (v t w) f
    simp only [v, g, Matrix.mulVecLin_apply, mulVec_mulVec, smul_neg, exp_mul_exp_neg, one_mulVec] at this
    simp only [v, smul_neg]
    exact this.symm
  have hL := fun t (ht : IsUnit (A t)) (Ai' : Eu l →L[ℝ] Eu l) (h : HasDerivAt (fun t => Ring.inverse (A t)) Ai' t) =>
    ld_big h (hd Sum.inl Sum.inr t) (hd Sum.inr Sum.inl t) (hcd t ht).hasDerivAt
      ((hopen t ht).mono fun u hu => ⟨hu.ringInverse, hc u hu⟩)
  have h0 : IsUnit (A 0) := A0 ▸ isUnit_one
  obtain ⟨ε, hε, hA⟩ := Metric.eventually_nhds_iff.1 (hopen 0 h0)
  simp only [dist_zero_right, Real.norm_eq_abs] at hA
  refine ⟨ε, V, fun t => Ring.inverse (V t), (deriv c 0 : ℝ) + ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ), hε,
    fun f => by rw [V0]; rfl, fun t ht => ⟨fun f => ?_, fun f => ?_, hI t (hA ht)⟩, fun t ht f lam => ?_, fun f lam => ?_⟩
  · rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ (hU t (hA ht)), ContinuousLinearMap.one_apply]
  · rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ (hU t (hA ht)), ContinuousLinearMap.one_apply]
  · obtain ⟨Q, hQ, -⟩ := hL t (hA ht) _ ((hd Sum.inl Sum.inl t).differentiableAt.inverse (hA ht)).hasDerivAt
    exact LL.LD.differentiableAt (V := V) hQ v (fun w a => (hv t w a).differentiableAt) ((hopen t (hA ht)).mono hw) f lam
  · have h1 : HasDerivAt (fun t => Ring.inverse (A t)) (-bl Sum.inl Sum.inl X) 0 := by
      have h2 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Eu l →L[ℝ] Eu l)ˣ)).comp_hasDerivAt_of_eq 0
        (hd Sum.inl Sum.inl 0) A0.symm
      exact h2.congr_deriv (by
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one,
          one_mul, mul_one, zero_smul, NormedSpace.exp_zero])
    obtain ⟨Q, hQ, hQ'⟩ := hL 0 h0 _ h1
    have h3 := hQ' (by rw [A0, Ring.inverse_one]) (by rw [← block_inl_inr_one, ← g0]) (by rw [← block_inr_inl_one, ← g0]) c0
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    set z : ℂ := (deriv c 0 : ℝ) + ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) with hz
    have h4 : Q = ⇑(quad X + z • (1 : Sch l →L[ℂ] Sch l)) := by
      funext f
      rw [h3, ContinuousLinearMap.add_apply, quad_eq hX, hz, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        add_smul]
      abel
    rw [h4] at hQ
    refine LL.LD.hasDerivAt (V := V) hQ (fun f => ?_) v (fun w => X *ᵥ w) (fun w => by simp [v]) (fun w a => ?_) (fun w => ?_)
      ((hopen 0 h0).mono hw) f lam
    · exact congrArg (fun T : Sch l →L[ℂ] Sch l => T f) V0
    · simpa [neg_mulVec] using hv 0 w a
    · rw [← quad_comm hX, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      abel

end PositivityTheory.ThKR
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.LocalLift =====
