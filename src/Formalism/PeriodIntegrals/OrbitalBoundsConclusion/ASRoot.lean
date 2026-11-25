module

public import Formalism.PeriodIntegrals.ArtSch
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArtinSchreierRoots.ExistsRootOC, Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArtinSchreierRoots.ExistsRootOC =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArtinSchreierRoots.ExistsRootOC", "h": "module\n\npublic import Formalism.PeriodIntegrals.ArtSch\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\npublic import Mathlib.RingTheory.Valuation.Integral\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace PI.ArtSch.RootWork

open Polynomial

variable (l : ℕ) [Fact l.Prime]

theorem exists_root_OC (c b : OC l) : ∃ z : OC l, z ^ l - c * z - b = 0 := by
  classical
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  let p : (OC l)[X] := X ^ l - (C c * X + C b)
  have hdeg : (C c * X + C b).degree < (X ^ l : (OC l)[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast (show 1 < l by omega))
  have hmon : p.Monic := (monic_X_pow l).sub_of_left hdeg
  have hnat : p.natDegree = l := by
    apply natDegree_eq_of_degree_eq_some
    rw [degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]
  let q : ℂ_[l][X] := p.map (algebraMap (OC l) ℂ_[l])
  have hq : q.degree ≠ 0 := by
    rw [degree_eq_natDegree (hmon.map _).ne_zero, (hmon.natDegree_map _), hnat]
    exact_mod_cast (show l ≠ 0 by omega)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hq
  have hx' : eval₂ (algebraMap (OC l) ℂ_[l]) x p = 0 := by
    rw [← eval_map]
    exact hx
  have hint : IsIntegral (OC l) x := ⟨p, hmon, hx'⟩
  have hmem : x ∈ PadicComplexInt l := (PadicComplexInt.integers l).mem_of_integral hint
  refine ⟨⟨x, hmem⟩, ?_⟩
  apply Subtype.ext
  have h2 : eval₂ (algebraMap (OC l) ℂ_[l]) x p = x ^ l - ((c : ℂ_[l]) * x + (b : ℂ_[l])) := by
    simp only [p, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C]
    rfl
  rw [h2] at hx'
  show x ^ l - (c : ℂ_[l]) * x - (b : ℂ_[l]) = 0
  rw [sub_sub]
  exact hx'

end PI.ArtSch.RootWork
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArtinSchreierRoots.ExistsRootOC =====

-- ===== clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot", "h": "module\n\npublic import Formalism.PeriodIntegrals.ArtSch\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArtinSchreierRoots.ExistsRootOC\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem rootModP_holds : PI.ArtSch.RootModP := by
  intro l _ c b
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, hz⟩ := PI.ArtSch.RootWork.exists_root_OC l c' b'
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [← map_pow, ← map_mul, ← map_sub, ← map_sub, hz, map_zero]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot =====
