module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.DivDeep

theorem root_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {z : M.Z}
    (hn : IsIntegrallyClosed (M.O z)) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : u ∈ M.O z := by
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

theorem exists_eq_smul_of_smul_eq_zero {L k : ℕ} (hL : 0 < L) (hk : k ∣ L) (a : ZMod L) (ha : k • a = 0) :
    ∃ x : ZMod L, (L / k) • x = a := by
  obtain ⟨d, rfl⟩ := hk
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hL)
  haveI : NeZero (k * d) := ⟨hL.ne'⟩
  rw [Nat.mul_div_cancel_left _ hk]
  have h : ((k * a.val : ℕ) : ZMod (k * d)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, ha]
  obtain ⟨e, he⟩ := Nat.dvd_of_mul_dvd_mul_left hk ((ZMod.natCast_eq_zero_iff _ _).1 h)
  exact ⟨e, by rw [nsmul_eq_mul, ← Nat.cast_mul, ← he, ZMod.natCast_zmod_val]⟩

end GlobalTheory.Poinc.DivDeep
