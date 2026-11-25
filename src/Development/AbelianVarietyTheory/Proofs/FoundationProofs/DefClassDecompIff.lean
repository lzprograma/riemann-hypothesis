module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.DoubleCosetDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
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

namespace GlobalTheory.DecompCompare

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers Matrix
open scoped TensorProduct

theorem frame_inv {n P Q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G P Q)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) :
    ∃ L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ, L * A = 1 ∧ A * L = 1 := by
  obtain ⟨A₀, L₀, h0, hl, hr⟩ := GlobalTheory.VolPairExists.exists_frame h
  obtain ⟨e, -⟩ := h
  have h1 : (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
    calc (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A
        = L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) := by simp only [Matrix.mul_assoc]
      _ = L₀ * Formalism.UG.Jpq P Q * (A₀ * L₀)ᴴ * Formalism.UG.Jpq P Q * A₀ := by
          rw [hA, ← h0, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = L₀ * (Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q) * A₀ := by
          rw [hr, Matrix.conjTranspose_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [GlobalTheory.VolPairExists.jpq_mul_self, Matrix.mul_one, hl]
  exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_equiv e).1 h1⟩

variable (D : D7)

theorem KSub_eq (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) :
    KSub D W P Q θ A = levelW D.sp.cm W := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, fun ρ => ?_⟩⟩
  have hsig : Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := by
    have := hW (embOf D ρ)
    rwa [hs] at this
  obtain ⟨L, hl, hr⟩ := frame_inv hsig (hA ρ)
  have hu : (infMat D.sp.cm.sig W.gram (θ ρ) h)ᴴ * W.gram.map (embOf D ρ) * infMat D.sp.cm.sig W.gram (θ ρ) h =
      W.gram.map (embOf D ρ) := GlobalTheory.FockCompare.RealAction.infMat_mem_UH (D := D) (θ := θ) hθ W h ρ
  refine ⟨GlobalTheory.VolPairExists.mkU _ (GlobalTheory.VolPairExists.conj_unitary (hA ρ) hr hu), Set.mem_univ _, ?_⟩
  rw [GlobalTheory.VolPairExists.mat_mkU, Matrix.mul_assoc, hl, Matrix.mul_one]

theorem exists_data (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q)) :
    (∃ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) ∧
    ∃ A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ) := by
  refine ⟨GlobalTheory.DualPairCompare.exists_infFam D, ?_⟩
  have hsig : ∀ ρ, Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := fun ρ => by
    have := hW (embOf D ρ)
    rwa [hs] at this
  choose A L hA _ using fun ρ => GlobalTheory.VolPairExists.exists_frame (hsig ρ)
  exact ⟨A, hA⟩

theorem isOpen_levelW (W : HSpace D.host.E) :
    IsOpen (levelW D.sp.cm W : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) :=
  GlobalTheory.StabOpen.isOpen_stab_latHat D W

end GlobalTheory.DecompCompare
