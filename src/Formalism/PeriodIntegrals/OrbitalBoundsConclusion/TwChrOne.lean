module

public import Formalism.PeriodIntegrals.TwChrOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain, Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain", "h": "module\n\npublic import Formalism.PeriodIntegrals.TwChrOne\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwChrOne.Pf

theorem twChrOne_main : PI.TwChrOne.TwChrOne := by
  intro E K _ _ _ _ P psi ξ kj N c hpsi

  have memJ : ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
      (1 : Sp E (N + c) ≃ₗ[E] Sp E (N + c)), r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c := by
    intro r hr
    unfold Loc.Cbe at hr
    have h2 := (Subgroup.mem_inf.mp hr).2
    rw [Subgroup.mem_comap] at h2
    simpa using h2

  have chi_eq : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      ChiL P psi ξ kj N c 1 r = (LocE.unitV ξ (Ment kj N c r).det)⁻¹ := by
    intro r hr
    unfold ChiL
    rw [hpsi _ (isIntegralAt_superdiagonalSum P (hI_of P hr)), inv_one, one_mul, inv_one, one_mul, mul_one]
    rfl
  have unit_of : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      IsUnit (redP P (Ment kj N c r).det) := by
    intro r hr
    rw [redP_det_Ment P (hI_of P hr)]
    exact isUnit_Mb P hr
  refine ⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · have hJ := memJ r hr
    rw [chi_eq r hJ]
    refine inv_ne_zero ?_
    unfold LocE.unitV
    rw [dite_eq_left (unit_of r hJ)]
    exact Units.ne_zero _
  · have hJ := memJ r hr
    have hJ' := memJ r' hr'
    have hJ'' := memJ r'' hr''
    rw [chi_eq r hJ, chi_eq r' hJ', chi_eq r'' hJ'', ← mul_inv]
    congr 1
    have hd : redP P (Ment kj N c r'').det =
        redP P (Ment kj N c r).det * redP P (Ment kj N c r').det := by
      rw [redP_det_Ment P (hI_of P hJ''), redP_det_Ment P (hI_of P hJ),
        redP_det_Ment P (hI_of P hJ'), ← Matrix.det_mul]
      congr 1
      apply Mb_mul_of P (fun i hi1 hi2 j hj => red_DA P hJ i hi1 hi2 j hj) (hI_of P hJ) (hI_of P hJ')
      intro t
      have ht : kj + t.1 < N := by have := t.isLt; omega
      have := hx (Loc.eN E N (kj + t.1))
      rwa [inX_eN ht] at this
    have hu := unit_of r hJ
    have hu' := unit_of r' hJ'
    have hu'' := unit_of r'' hJ''
    unfold LocE.unitV
    rw [dite_eq_left hu'', dite_eq_left hu, dite_eq_left hu']
    have hmul : hu''.unit = hu.unit * hu'.unit := Units.ext (by simp [hd])
    rw [hmul, map_mul, Units.val_mul]

end PI.TwChrOne.Pf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain =====

-- ===== clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne", "h": "module\n\npublic import Formalism.PeriodIntegrals.TwChrOne\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

alias TwChrOne := _root_.PI.TwChrOne.Pf.twChrOne_main
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne =====
