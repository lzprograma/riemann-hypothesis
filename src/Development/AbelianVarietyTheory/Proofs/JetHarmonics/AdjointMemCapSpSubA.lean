module

public import Formalism.HermitianCurvature.FrameExists2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntertwinerDOpOfStabiliser
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem adjoint_mem_CapSp_subA : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (T : V₂ →L[ℂ] V₁) (μ : Fin n → ℂ), IsRepW (n + 1) r z π₁ → IsRepW (n + 1) r z π₂ → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₁ h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₂ h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → (∀ h ∈ UWset (n + 1) r z, h *ᵥ B (Fin.last n) = B (Fin.last n) → T.comp (π₂ h) = (π₁ h).comp T) → ∀ v ∈ CapSp (subA (EB π₁ B)) μ, ContinuousLinearMap.adjoint T v ∈ CapSp (subA (EB π₂ B)) μ := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ B T μ h₁ h₂ hu₁ hu₂ hB hT v hv
  have hB' : IsFrameOf (n + 1) r [z, B (Fin.last n)] (fun a : Fin n => B a.castSucc) := by
    refine ⟨fun a => hB.1 _, fun a b => ?_, fun a x hx => ?_⟩
    · rw [hB.2.1]
      simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact hB.2.2 _ x (by simp [hx])
      · rw [hx, hB.2.1, ite_eq_right (Fin.castSucc_lt_last a).ne]
  have hlie := GlobalTheory.intertwiner_EB_of_stabiliser V₂ V₁ (n + 1) r n z (B (Fin.last n)) π₂ π₁ T
    (fun a : Fin n => B a.castSucc) h₂ h₁ hB' (fun h hh he w => by
      have := congrArg (fun S : V₂ →L[ℂ] V₁ => S w) (hT h hh he)
      simpa using this)
  have hlie' : ∀ (a b : Fin n) (w : V₂),
      T (EB π₂ B a.castSucc b.castSucc w) = EB π₁ B a.castSucc b.castSucc (T w) := hlie
  have hadj : ∀ (a b : Fin n) (w : V₁),
      (ContinuousLinearMap.adjoint T).toLinearMap (subA (EB π₁ B) a b w) =
        subA (EB π₂ B) a b ((ContinuousLinearMap.adjoint T).toLinearMap w) := by
    intro a b w
    apply ext_inner_right ℂ
    intro y
    show inner ℂ (ContinuousLinearMap.adjoint T (EB π₁ B a.castSucc b.castSucc w)) y =
      inner ℂ (EB π₂ B a.castSucc b.castSucc (ContinuousLinearMap.adjoint T w)) y
    rw [ContinuousLinearMap.adjoint_inner_left,
      Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₁.1 h₁.2 hu₁ hB, Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₂.1 h₂.2 hu₂ hB,
      ContinuousLinearMap.adjoint_inner_left, hlie']
  rw [mem_CapSp] at hv ⊢
  intro w
  have hq := qminor_intertwine V₂ V₁ n n (subA (EB π₂ B)) (subA (EB π₁ B))
    (ContinuousLinearMap.adjoint T).toLinearMap hadj id id w v
  have hq' : ContinuousLinearMap.adjoint T (qdet (subA (EB π₁ B)) w v) =
      qdet (subA (EB π₂ B)) w (ContinuousLinearMap.adjoint T v) := hq
  rw [← hq', hv w, map_smul]

end GlobalTheory
