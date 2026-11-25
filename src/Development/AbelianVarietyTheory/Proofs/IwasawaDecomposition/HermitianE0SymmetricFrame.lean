module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix

namespace GlobalTheory.Mem.SymChar

theorem hA_e0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg b j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 b).1
    · exact ((X.weightVectorsIntegral _).2.2 b).2.2.1
  refine wInt_of_zmod X kv.1 hg ?_
  have hb := b.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, ite_eq_right (by omega), sub_zero]; exact (X.gramIntegral _ _).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2, ite_eq_right (by omega), sub_zero]; exact hW _
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, ite_eq_right (by omega), sub_zero]; exact (X.formsAtZero.2 b).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3]
    have h := (X.gramIntegral b ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩).2.2
    by_cases e : j.1 = 2 * D.R.rS + D.R.k - b.1
    · rw [ite_eq_left e]
      rwa [ite_eq_left (Fin.ext (by simp only; omega))] at h
    · rw [ite_eq_right e]
      rwa [ite_eq_right (fun h' => e (by have := congrArg Fin.val h'; simp only at this; omega))] at h
  · rw [dite_eq_right h3, ite_eq_right (by omega), sub_zero, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
