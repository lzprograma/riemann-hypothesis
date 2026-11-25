module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairingStatement
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

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem map_infOf_true {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) :
    Multiset.map (PositivityTheory.RgBcC.infOf l.w true) Finset.univ.val = infOfWeight l := by
  unfold infOfWeight
  refine Multiset.map_congr rfl fun k _ => ?_
  simp [PositivityTheory.RgBcC.infOf]
  try ring

theorem map_infOf_false {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) :
    Multiset.map (PositivityTheory.RgBcC.infOf l.w false) Finset.univ.val = (infOfWeight l).map Neg.neg := by
  unfold infOfWeight
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp [PositivityTheory.RgBcC.infOf]
  try ring

theorem aux_statement_11 (hG : ThetaFixedGlobalCharacter) (hθ : ThetaFixOf) : ThetaFixedGlobalWeights := by
  intro E _ _ _ n hn π hreg hd lamE hl K h1 h2 h3 h4 _ _ μC _ _ _ μf _ μ _
  refine hG E n hn π hreg (hθ E n hn π hd) (fun w => (lamE w.embedding).w) (fun w => (lamE w.embedding).anti) (fun w => ⟨?_, ?_⟩)
    K h1 h2 h3 h4 μC μf μ
  · rw [map_infOf_true]
    exact hl _
  · rw [map_infOf_false, ← GlobalTheory.CapPair.infChar_conj_of_paired E n π π hd w.embedding _ _ (hl _) (hl _)]
    exact hl _

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
