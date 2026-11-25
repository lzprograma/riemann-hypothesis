module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TrdegPf

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem eq_of_choose_eq_one_of_pos {r D : ℕ} (hD : 0 < D) (h : r.choose D = 1) : D = r :=
  ((Nat.choose_eq_one_iff.mp h).resolve_left hD.ne').symm

theorem trBasis_of_isFreeGen_dForm : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q), 0 < D →
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) → TrBasis cL (fun i => (x i : L)) := by
  intro L _ cL Q hQ D x hD hx
  letI := cL.toAlgebra
  let c0 : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  letI := c0.toAlgebra
  haveI : IsScalarTower ℂ Q L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing Q L := IsFractionRing.of_field Q L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e]
  haveI : Algebra.FormallyEtale Q L := .of_isLocalization (nonZeroDivisors Q)
  have hL : IsFreeGen L (TopForm.formMap D Q.subtype rfl (dForm c0 x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q L) D)
  rw [TopForm.formMap_dForm] at hL
  change IsFreeGen L (dForm cL fun i => (x i : L)) at hL

  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : Algebra.EssFiniteType Q L := .of_isLocalization L (nonZeroDivisors Q)
  haveI : Algebra.EssFiniteType ℂ L := .comp ℂ Q L
  have h1 : Module.finrank L (Forms cL D) = 1 := by
    have e : L ≃ₗ[L] Forms cL D := LinearEquiv.ofBijective (LinearMap.toSpanSingleton L _ _) hL
    rw [← e.finrank_eq, Module.finrank_self]
  rw [exteriorPower.finrank_eq] at h1
  have hr := eq_of_choose_eq_one_of_pos hD h1

  have hli : LinearIndependent L fun i => KaehlerDifferential.D ℂ L (x i : L) := by
    by_contra hc
    have h0 : dForm cL (fun i => (x i : L)) = 0 := by
      rw [dForm_eq]
      exact (exteriorPower.ιMulti L D).map_linearDependent _ hc
    rw [h0] at hL
    exact one_ne_zero (hL.1 (a₁ := 1) (a₂ := 0) (by simp))
  have hind : AlgebraicIndependent ℂ fun i => (x i : L) :=
    ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence ℂ L D _ hli
  have htr : Algebra.trdeg ℂ L = D := by
    rw [← rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank]
    exact_mod_cast hr.symm
  exact hind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr, Cardinal.mk_fin])

end GlobalTheory.FieldPair
