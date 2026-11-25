module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
public import Formalism.DoubleCosetMeasures.LatticeCoset
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.TypeStar
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.NumberTheory.RamificationInertia.Basic
import Formalism.DoubleCosetMeasures.Statement

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus\npublic import Mathlib.Analysis.Normed.Unbundled.RingSeminorm\npublic import Mathlib.Analysis.Matrix.MeasurableSpace\npublic import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint\npublic import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni\npublic import Formalism.DoubleCosetMeasures.LatticeCoset\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProd\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\npublic import Mathlib.Tactic.Linter.HaveILetI\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem mem_aboveF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)} :
    P ∈ aboveF (L := D.host.E) D.host.F v ↔ P.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

theorem prime_eq_of_overP {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h : ((a * p + b * q : ℤ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast h1))
      (w.asIdeal.mul_mem_left _ (by exact_mod_cast h2))
  rw [hab, Int.cast_one] at h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_qp (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {p : ℕ | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}.Finite := by
  have hs : ∀ w : HeightOneSpectrum (𝓞 D.host.E), Set.Subsingleton {p : ℕ | p.Prime ∧ OverP D.host p w} :=
    fun w p hp q hq => prime_eq_of_overP hp.1 hq.1 hp.2 hq.2
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).biUnion fun w _ => (hs w).finite).subset ?_
  rintro p ⟨hp, w, hw, hr⟩
  exact Set.mem_biUnion hr ⟨hp, hw⟩

def qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Finset ℕ := (finite_qp Tp μ).toFinset

theorem mem_qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ qpSet Tp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := by
  rw [qpSet, Set.Finite.mem_toFinset]; rfl

theorem ramifiedRationalPrimesOfTuple_baseTuple_eq_empty (Tp : TupTied D C nch) : qpSet Tp D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨-, w, -, hr⟩ := (mem_qpSet Tp _ p).1 hp
  exact hr fun x _ => by rw [Tp.trueColumnChoices_heckeChar_reference_eq_one]; rfl

theorem qpSet_muAt (Tp : TupTied D C nch) (hp : TupPins Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ qpSet Tp (D.what₂.muAt w) := fun h => by
  obtain ⟨-, w', hw', hr⟩ := (mem_qpSet Tp _ _).1 h
  exact hr (hp.atl w w' hw')

variable (Tp : TupTied D C nch) (hp : TupPins Tp)

def reQ (_Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (Z₀ : DivX D) : DivX D :=
  { Z₀ with
    Qp := qpSet Tp
    degreeZero_partial_set_empty := ramifiedRationalPrimesOfTuple_baseTuple_eq_empty Tp
    Qp_muAt := qpSet_muAt Tp hp
    QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
    qv := fun _ v => Ideal.absNorm v.1.asIdeal }

def reducedDivisorCharacter (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (Z₀ : DivX D) : DivisorCharacterCompatibility D C nch Tp (reQ Tp hp Pv Z₀) where
  Qp_iff := mem_qpSet Tp
  eQPl := fun _ => Equiv.refl _
  qv_eq := fun _ _ => rfl

end GlobalTheory.Mem.HD.ReQ
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty =====
