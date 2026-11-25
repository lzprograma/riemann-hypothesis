module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.AdeleApproximation.AdeleIntA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.DenseRangeFiniteAdele


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.MemZeroLocusGLIff, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.MemZeroLocusGLIff =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.MemZeroLocusGLIff", "h": "module\n\npublic import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain

namespace PI.UnipApproxD

def AddDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F))

end PI.UnipApproxD
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.MemZeroLocusGLIff =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.MemZeroLocusGLIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.DedekindDomain.Factorization\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.AdeleApproximation.AdeleIntA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.UnipApproxD.IntegersDenseFiniteAdeles

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA (exists_approx exists_approx_adele)

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_small (v : HeightOneSpectrum R) {U : Set (v.adicCompletion K)}
    (hU : U ∈ nhds (0 : v.adicCompletion K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : v.adicCompletion K, Valued.v y ≤ v.intValuation r → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  have hpos : (0 : WithZero (Multiplicative ℤ)) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.mpr γ.ne_zero)
    simpa using this
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hpos.ne'
  have hI : v.asIdeal ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨r, hrI, hr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨r, hr, fun y hy => hγ ?_⟩
  show Valued.v.restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt (hy.trans ((v.intValuation_le_pow_iff_mem r k).mpr hrI)) hk

theorem denseRange : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by
  apply _root_.ReciprocityTheory.ChartRestriction.G.SA.denseRange_finiteAdele <;> assumption

end PI.UnipApproxD.IntegersDenseFiniteAdeles

namespace PI.UnipApproxD

open NumberField IsDedekindDomain

theorem additive_dense_integers : AddDense := by
  intro F _ _
  exact IntegersDenseFiniteAdeles.denseRange

end PI.UnipApproxD
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense =====
