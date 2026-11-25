module

public import Aesop.BuiltinRules
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowEqThetaLevelChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

namespace GlobalTheory.ThetaGAGA

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ}

theorem top_le_of_lbPow (u : HolUnif A M g) (k : ℕ) (j : (lbPow M k).ι) {z : Fin g → ℂ}
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow M k).U j) : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) :=
  GlobalTheory.top_le_preimage_mono _ (GlobalTheory.Cartier.lbPow_U M k j).le hz

def powFrame (u : HolUnif A M g) (k : ℕ) : HolUnif A (lbPow M k) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j z := u.fr (j PUnit.unit) z ^ k
  fr_hol j := ((u.fr_hol (j PUnit.unit)).mono fun _ hz => top_le_of_lbPow u k j hz).pow k
  fr_ne j z hz := pow_ne_zero _ (u.fr_ne _ z (top_le_of_lbPow u k j hz))
  fr_compat i j z hz := GlobalTheory.ThetaBundleSec.fr_pow_compat u z k i j
    ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).1 ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).2

theorem exists_isFnPow : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  intro g A _ hA M u Hm χ hM hAH k θ hθ
  have := hA.comm
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := GlobalTheory.HolUnifSec.exists_isFn (powFrame u k) hA hp (GlobalTheory.isLB_lbPow hM k) hθ.1 (by
    intro l hl j z hz
    have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) := top_le_of_lbPow u k j hz
    have h1 := hθ.2 ⟨l, hl⟩ z
    have h2 := hAH.2.2.2 ⟨l, hl⟩ _ z hz'
    change θ (z + l) * u.fr (j PUnit.unit) (z + l) ^ k = θ z * u.fr (j PUnit.unit) z ^ k
    simp only [hermForm] at h1
    change θ (z + l) = _ at h1
    change u.fr (j PUnit.unit) z = _ * u.fr (j PUnit.unit) (z + l) at h2
    rw [h1, h2, mul_pow]
    ring)
  exact ⟨s, hs⟩

end GlobalTheory.ThetaGAGA
