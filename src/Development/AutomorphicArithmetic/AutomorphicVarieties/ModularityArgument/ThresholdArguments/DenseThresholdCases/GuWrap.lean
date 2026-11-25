module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BciNarrowSwap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalUnitaryT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
namespace UpperTheory.V.Z.Win.Gu
theorem spehOf_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : GlobalTheory.BcSpeh.BcSpeh :=
  _root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge H.litN.aut.bc H.litN.loc.bern)
theorem galUnitaryT_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → GalUnitaryT := fun H => _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH_of_bcSpeh_of_rT H (_root_.UpperTheory.V.Z.Win.Gu.spehOf_alt H) (_root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal)
theorem endShape'_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → IsSSRep ρ → (∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → LocGlobT ι ρ w τ) → ∃ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, G E Ω →* GL (Fin (d i)) (Qbar l)), (∀ i, 1 ≤ d i ∧ 1 ≤ m i ∧ Continuous (ρ' i)) ∧ (∀ g, (UpperTheory.V.W.mat ρ g).charpoly = ∏ i, ∏ j ∈ Finset.range (m i), (UpperTheory.V.W.mat (UpperTheory.V.Af.tw (ρ' i) (cycBar E Ω l ^ (-(j : ℤ)))) g).charpoly) ∧ ((∀ i, m i = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ b : Multiset ℂ, UpperTheory.V.Af.FrobEig ι ρ w b → ∀ z ∈ b, ∀ z' ∈ b, ‖z‖ < (normV w : ℝ) * ‖z'‖) :=
  fun H => _root_.UpperTheory.V.Z.Win.Gu.endShapeT' H (_root_.UpperTheory.V.Z.Win.Gu.spehOf_alt H) (_root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal)
end UpperTheory.V.Z.Win.Gu
end
