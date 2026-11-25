module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbedding
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoin

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree, Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound\nimport Mathlib.Algebra.AffineMonoid.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.KrullDimension.PID\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.DecompCard

theorem card_stabilizer_eq_locDeg : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l →
    Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  intro l _ E _ _ _ v w hv hw
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have := v.isPrime
  have := w.isPrime
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), R ∈ placesOver E l →
      R.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hR)
  have := hover v hv
  have := hover w hw
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) (Ideal.span {(l : ℤ)}) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E), locDeg]

end GlobalTheory.DecompCard
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree\npublic import Formalism.SharpRestriction.LevelLetterCocycles.DataN\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbedding\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Mathlib.NumberTheory.Padics.Complex\npublic import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas\npublic import Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoin\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_degW {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N)
    (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) :
    Br.DegW nbr i w hw := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl (N.l i) := (nbr i w hw).j.comp (algebraMap H.E N.Om)
  have hK : (nbr i w hw).Kw.1 = IntermediateField.adjoin ℚ_[N.l i] (Set.range c) :=
    _root_.GlobalTheory.padicAlgCl_finite_dense_eq_adjoin (N.l i) H.E c (nbr i w hw).Kw.1 (nbr i w hw).j_E (nbr i w hw).Kw.2
      (nbr i w hw).j_dense
  obtain ⟨v, hv, hc⟩ := _root_.GlobalTheory.LocPlace.exists_place_of_emb (N.l i) H.E c
  have h1 := _root_.UpperTheory.HF.LocStab.finrank_adjoin_range_eq_card_stabilizer (N.l i) H.E c v hc
  have h2 := _root_.GlobalTheory.DecompCard.card_stabilizer_eq_locDeg (N.l i) H.E v w hv hw
  have h3 : Module.finrank ℚ_[N.l i] (nbr i w hw).Kw.1 = locDeg H.E w := by
    rw [hK, h1, h2]
  exact h3

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia =====
