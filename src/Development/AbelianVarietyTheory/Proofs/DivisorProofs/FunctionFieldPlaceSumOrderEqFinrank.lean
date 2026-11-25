module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.FunctionField.PlaceSum
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.FunctionField.PlaceAbove

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.FundId

variable {k F : Type} [Field k] [Field F] [Algebra k F]

noncomputable def toRing (v : Place k F) : GroundTheory.FunctionField.Place k F where
  ring := v.1.valuationSubring
  ne_top := by
    intro h
    obtain ⟨x, hx⟩ := v.2.1 (WithZero.exp 1)
    have hm : x ∈ v.1.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hm
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.2.2 c hc).le

theorem valuation_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) :
    (toRing v).valuation = v.1 := by
  refine GroundTheory.FunctionField.valuation_eq_of_isEquiv ?_ (toRing v).valuation_surjective v.2.1
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [GroundTheory.FunctionField.Place.valuation_le_one_iff]
  rfl

theorem ord_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) (x : F) :
    (toRing v).ord x = ord v x := by
  unfold ord
  rw [← valuation_toRing]
  rfl

theorem toRing_injective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Injective (toRing : Place k F → _) := fun v w h =>
  Subtype.ext (by rw [← valuation_toRing, ← valuation_toRing, h])

theorem toRing_surjective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Surjective (toRing : Place k F → _) := by
  intro w
  refine ⟨⟨w.valuation, w.valuation_surjective, fun c hc => ?_⟩, ?_⟩
  · exact w.valuation_algebraMap' hc
  · ext x
    exact w.valuation_le_one_iff x

theorem deg_eq_one [IsAlgClosed k] [GroundTheory.FunctionField.IsFunctionField k F]
    (w : GroundTheory.FunctionField.Place k F) : w.deg = 1 := by
  have h : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have e : k ≃ₗ[k] w.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap k w.ResidueField) h
  have := e.finrank_eq
  rw [Module.finrank_self] at this
  exact this.symm

theorem sum_ord_eq_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hF ρ hρ v π _ hπ
  classical
  haveI : GroundTheory.FunctionField.IsFunctionField k F := ⟨hF⟩
  haveI : GroundTheory.FunctionField.IsFunctionField k E :=
    GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional (k := k) (K := F)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have key : ∀ p : Place k E, ρ p = v ↔ (toRing p).LiesOver (toRing v) := by
    intro p
    have h1 : (toRing p).LiesOver (toRing (ρ p)) := by
      ext x
      exact hρ p x
    constructor
    · rintro rfl; exact h1
    · intro h
      exact toRing_injective (GroundTheory.FunctionField.Place.ext (h1.symm.trans h))
  have hfin := (toRing v).finite_liesOver (K' := E)
  have hfin' : {p | ρ p = v}.Finite := by
    refine (hfin.preimage toRing_injective.injOn).subset fun p hp => (key p).1 hp
  refine ⟨hfin', ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', ← (toRing v).sum_ramificationIdx_mul_inertiaDeg (K' := E),
    Nat.cast_sum]
  refine Finset.sum_bij (fun p _ => toRing p) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [key] using hp
  · intro p _ q _ h
    exact toRing_injective h
  · intro w hw
    obtain ⟨p, rfl⟩ := toRing_surjective w
    exact ⟨p, by simpa [key] using hw, rfl⟩
  · intro p hp
    have h : (toRing p).LiesOver (toRing v) := by simpa [key] using hp
    rw [← ord_toRing, h.ord_algebraMap, ord_toRing, hπ, GroundTheory.FunctionField.Place.inertiaDeg,
      deg_eq_one, deg_eq_one]
    simp

end GlobalTheory.Nef.FundId
