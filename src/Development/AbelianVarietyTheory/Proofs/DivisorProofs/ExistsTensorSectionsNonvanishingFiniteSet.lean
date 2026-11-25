module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

noncomputable section

namespace GlobalTheory.MixHt

theorem exists_tens_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite →
      ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  intro k _ Y q hq M S hS
  have := hq.isNoetherian
  obtain ⟨N, j, hj, e⟩ := hq.isProjOver
  let A₀ : HermLB q := (ProjSpace.hermitianTwistingSheaf k N).pull j e
  have hA : IsAmpleLB A₀.B := by
    dsimp [A₀, HermLB.pull, ProjSpace.hermitianTwistingSheaf, HermLB.fs]
    exact (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  obtain ⟨n, h₁, h₂⟩ := (tendsto_natCast_atTop_atTop.eventually
    ((hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS).and
      (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv Y) hS))).exists
  obtain ⟨s, hs⟩ := h₁ (CechPic.tens M.B (lbPow A₀.B n)) (isLB_tens M.isLB (isLB_lbPow A₀.isLB n)) (by
    rw [cls_tens M.isLB (isLB_lbPow A₀.isLB n), cls_lbPow A₀.isLB, natCast_zsmul])
  obtain ⟨u, hu⟩ := h₂ (lbPow A₀.B n) (isLB_lbPow A₀.isLB n) (by
    rw [cls_lbPow A₀.isLB, cls_triv, zero_add, natCast_zsmul])
  exact ⟨A₀.pow n, s, u, hs, hu⟩

end GlobalTheory.MixHt
