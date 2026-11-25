module

public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousHsInner
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransportPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordCorrespondence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelIntegralStep

theorem uInv_at_zero {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv 0 w x = x
  | [], x => rfl
  | l :: w, x => by
    funext e
    have key : ∀ a : Fin 2, e (0 : Fin (w.length + 1)) = a →
        (Fin.cons a (fun b : Fin w.length => e b.succ) : Fin (w.length + 1) → Fin 2) = e := by
      intro a ha
      funext b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp [ha]
      · simp
    simp only [KB.uInv, uInv_at_zero w, map_zero, ite_self, zero_smul, add_zero]
    split_ifs with h0
    · exact congrArg x (key 0 h0)
    · refine congrArg x (key 1 ?_)
      have : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
      exact this _ h0

theorem fsv_at_zero (t : ℂ) : P5.fsv 0 t = 1 := by simp [P5.fsv]

theorem waveG_at_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp only [KB.waveG, fsv_at_zero, one_smul, uInv_at_zero]

theorem levelForm_eq_integral : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (j : ℕ) (h : C.LPt), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → j ≤ P.r → D.IsLocPt h j → Integrable (fun t : ℂ => (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)])) ∧ p.RR H j w h h = ∫ t : ℂ, (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)]) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w j h hCb hH hw hj hh
  obtain ⟨φ, -, hφi, hφe, hφs⟩ := Formalism.FourierDecayAlt.P.PBO.pStd_of_cpt hP Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top Formalism.FourierDecayAlt.P.PBF.formOne Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar (Formalism.FourierDecayAlt.P.PBO.topContOn_of hP Formalism.FourierDecayAlt.P.head_top) Wp Wq P p H j hj w h h hh hh Cb hCb hH hw
  have hae : φ =ᵐ[volume] fun t : ℂ =>
      (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)]) := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht using hφe t ht
  refine ⟨hφi.congr hae, ?_⟩
  have h1 := hφs 0
  simp only [fsv_at_zero, one_mul, waveG_at_zero] at h1
  rw [Formalism.FourierDecayAlt.P.PBL.rr_eq_form p H j hj w h h hh hh, ← h1]
  exact integral_congr_ae hae

end GlobalTheory.LevelIntegralStep
