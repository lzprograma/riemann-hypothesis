module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubOneIffEntries
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SeeConjRead
open Classical

theorem cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ} (f : Fin m → Formalism.L2.SG.HidaSetting.VA I)
    (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
    (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
  subst h
  exact hf a

theorem cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
  subst h
  exact hv

theorem flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M)
    (z : M) (he : ∀ a, e a ∈ S) (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
    flagV ρ k n e f b z i ∈ S := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, h0]

theorem colMat_entry {D : D7} {n : ℕ} (M : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (M * colMat w) i j = Matrix.mulVec M (w j) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]

end GlobalTheory.SeeConjRead
