module

public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis

namespace GlobalTheory.SiegelFormula.Model

variable {D : D7}

theorem two_mul_finrank_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) (W : Submodule E B.V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

theorem bddAbove_witt {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_le B W hW; omega⟩

end GlobalTheory.SiegelFormula.Model

end
