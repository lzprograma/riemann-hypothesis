module

import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped Pointwise

namespace GlobalTheory.IndexVolume

theorem relIndex_mul_measure_subgroup {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  first | exact _root_.Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure | exact @_root_.Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure | apply _root_.Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure <;> assumption

theorem volGL_of_subset_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    (ν : Measure k) (s : Set (GL n k)) (hs : MeasurableSet s) (hK : s ⊆ KO k n) :
    volGL ν n s = volM ν n n (Units.val '' s) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  intro g hg
  obtain ⟨u, rfl⟩ := hK hg
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]

theorem relIndex_mul_volM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (n : Type) [Fintype n] [DecidableEq n] (H L : Subgroup (GL n k)),
    H ≤ L → L ≤ KO k n → IsOpen (H : Set (GL n k)) →
    0 < (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal ∧
    (H.relIndex L : ℝ) * (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal =
      (volM ν n n (Units.val '' (L : Set (GL n k)))).toReal := by
  intro k _ _ _ _ _ _ ν _ n _ _ H L hHL hLK hH
  obtain ⟨hB, hlc, hsc, hc, -, -, hhaar, -⟩ := volGL_haar k n ν
  have hL : IsOpen (L : Set (GL n k)) := Subgroup.isOpen_mono hHL hH
  have hLc : IsCompact (L : Set (GL n k)) := hc.of_isClosed_subset (L.isClosed_of_isOpen hL) hLK
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  haveI : Finite (L ⧸ H.subgroupOf L) :=
    Subgroup.quotient_finite_of_isOpen _ (hH.preimage continuous_subtype_val)
  haveI : (H.subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have key := relIndex_mul_measure_subgroup H L hHL hH.measurableSet (volGL ν n)
  have h0 : volGL ν n H ≠ 0 := (hH.measure_pos _ ⟨1, one_mem _⟩).ne'
  have ht : volGL ν n H ≠ ⊤ := ((measure_mono (hHL.trans hLK)).trans_lt hc.measure_lt_top).ne
  rw [← volGL_of_subset_KO ν _ hH.measurableSet (hHL.trans hLK),
    ← volGL_of_subset_KO ν _ hL.measurableSet hLK, ← key]
  refine ⟨ENNReal.toReal_pos h0 ht, ?_⟩
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end GlobalTheory.IndexVolume
