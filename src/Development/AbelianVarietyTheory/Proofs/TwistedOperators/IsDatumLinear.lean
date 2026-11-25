module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
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

namespace GlobalTheory.SquareAgree

theorem isDatum_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), IsDatum M ψ crd 0 0 ∧ ∀ (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ) (c : ℂ), IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + c • Φ') (f + c • f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd
  have hn : ∀ x, ‖ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  refine ⟨⟨Submodule.zero_mem _, fun u => ?_⟩, fun Φ Φ' f f' c h h' =>
    ⟨Submodule.add_mem _ h.1 (Submodule.smul_mem _ c h'.1), fun u => ?_⟩⟩
  · have e : M.co.rho ψ u (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := funext fun x => by
      simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    rw [e]
    simp [GlobalTheory.WeilM.thetaSum]
  · have s1 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h.1).1 (M.co.e u)
    have s2 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ' (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h'.1).1 (M.co.e u)
    have e : M.co.rho ψ u (Φ + c • Φ') = M.co.rho ψ u Φ + c • M.co.rho ψ u Φ' := funext fun x => by
      simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← h.2 u, ← h'.2 u]
    unfold GlobalTheory.WeilM.thetaSum
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [s1.tsum_add (s2.mul_left c), tsum_mul_left]

end GlobalTheory.SquareAgree
