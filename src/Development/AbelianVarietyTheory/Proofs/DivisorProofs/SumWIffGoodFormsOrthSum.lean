module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 IsGenericPsi mem_primesOf)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.SumWCompare

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def cj (E : Type) [Field E] [StarRing E] : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := RingOfIntegers.ext (star_star (x : E))

theorem cj_algMap (hc : CMData F E) (x : 𝓞 F) : cj E (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
  RingOfIntegers.ext ((hc.fixed _).2 ⟨x, rfl⟩)

theorem exists_norm (hc : CMData F E) (y : 𝓞 E) : ∃ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) x = y * cj E y := by
  obtain ⟨a, ha⟩ := (hc.fixed ((y * cj E y : 𝓞 E) : E)).1 (by
    rw [← cj_coe, map_mul, cj_cj, mul_comm])
  have hi : IsIntegral ℤ a := by
    have h1 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact (y * cj E y).isIntegral_coe
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨a, hi⟩, RingOfIntegers.ext ha⟩

end Places

variable {D : D7}

theorem goodAt_comp {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ} {ι κ J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ))
    (e : ι → κ) (he : Function.Surjective e) (s : κ → LevelCuspCharacters.SSParam p K r) :
    LevelCuspCharacters.GoodAt χ (fun v => s (e v)) ↔ LevelCuspCharacters.GoodAt χ s := by
  simp only [LevelCuspCharacters.GoodAt, he.forall, he.exists]

theorem coeff_centralIdem {G : Type} [Group G] [Finite G] (τ : G → ℂ) (x : G) :
    (LevelCuspCharacters.centralIdem τ).coeff x = τ 1 / (Nat.card G : ℂ) * τ x⁻¹ := by
  classical
  unfold LevelCuspCharacters.centralIdem
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

end GlobalTheory.SumWCompare
