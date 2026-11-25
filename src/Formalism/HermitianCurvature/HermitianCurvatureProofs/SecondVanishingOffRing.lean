module

public import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeAverageIdentity

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm, Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm", "h": "module\n\npublic import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x1

theorem lamN_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (j : ℕ) (hj : j + 1 = n) : lamN R Z j = lamLin R Z := by
  unfold lamN lamTil lamLin rowN lastCoord
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  have : (a.val = j ↔ a.val + 1 = n) := by omega
  simp [this]

end Formalism.FourierDecayAlt.P.A5x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x1

theorem tripleForm : Formalism.FourierDecayAlt.A5.TripleForm := by
  intro K _ R ψ w w' k hw hw'
  unfold Kp intTT pairTerm
  apply finsum_congr
  intro q
  congr 2
  split_ifs with hI
  · congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro φ
    constructor
    · intro hφ
      refine ⟨hφ, ?_⟩
      intro j hkj hjn
      have hj : j = k := by omega
      subst hj
      refine ⟨0, ?_⟩
      intro v v' hv
      have h2 := hφ.2 v v' hv
      rw [lamN_last R _ j hw'.symm, lamN_last R _ j hw.symm, h2]
      simp
    · exact fun h => h.1
  · rfl

end Formalism.FourierDecayAlt.P
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing", "h": "module\n\npublic import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeAverageIdentity\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem second_gram_and_vanishing : Formalism.FourierDecayAlt.A5.A2 :=
  second_gram_vanishing_of_parts kernel_gram_property modulus_positive_multiplicative tripleForm
    lattice_average_identity triple_form_end_identity

theorem second_vanishing_off_ring : Formalism.FourierDecayAlt.A5.BlockKernelSupport := second_gram_and_vanishing.2

end Formalism.FourierDecayAlt.P
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing =====
