module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

namespace GlobalTheory.ClearDen

theorem exists_pow_mul_eq_val : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens), IsAffineOpen U → ∀ (r : Γ(A.left, U)) (k : (Fin g → ℂ) → ℂ), IsReg u.ex (A.left.basicOpen r) k → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, U), ∀ z ∈ pre u.ex (A.left.basicOpen r), val u.ex U b z = val u.ex U r z ^ N * k z := by
  intro A _ g L u U hU r k ⟨f, hf⟩
  have hloc := hU.isLocalization_basicOpen r
  obtain ⟨⟨b₀, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers r) f
  simp only at hb
  refine ⟨n, fun N hN => ⟨r ^ (N - n) * b₀, fun z hz => ?_⟩⟩
  have hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := GlobalTheory.top_le_preimage_mono _ (A.left.basicOpen_le r) hz
  have key : ∀ c : Γ(A.left, U), val u.ex (A.left.basicOpen r) (algebraMap Γ(A.left, U) Γ(A.left, A.left.basicOpen r) c) z = val u.ex U c z := by
    intro c
    exact GlobalTheory.valAt'_map _ (homOfLE (A.left.basicOpen_le r)).op c hz
  have e0 := congrArg (fun y => val u.ex (A.left.basicOpen r) y z) hb
  have e1 : val u.ex (A.left.basicOpen r) f z * val u.ex U r z ^ n = val u.ex U b₀ z := by
    rw [← key b₀, ← e0]
    unfold val
    rw [GlobalTheory.valAt'_mul]
    congr 1
    have := key (r ^ n)
    unfold val at this
    rw [this, GlobalTheory.valAt'_pow _ hzU]
  have e2 : val u.ex U (r ^ (N - n) * b₀) z = val u.ex U r z ^ (N - n) * val u.ex U b₀ z := by
    unfold val
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hzU]
  rw [e2, ← e1, hf z hz, ← Nat.sub_add_cancel hN, pow_add, Nat.add_sub_cancel]
  ring

end GlobalTheory.ClearDen
