module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu UpperTheory.Zero.LLC

open scoped commutatorElement

namespace UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem pow_iff (x : WD h) (σ : Weil h) :
    x.charPol σ = (X - 1) ^ x.lpDim ↔ ∀ α ∈ x.eig σ, α = 1 := by
  constructor
  · intro hx α hα
    rw [WD.eig, hx, ← C_1, roots_pow, roots_X_sub_C] at hα
    simpa using Multiset.mem_of_mem_nsmul hα
  · intro hx
    rw [WD.charPol_eq_prod, Multiset.eq_replicate_of_mem hx, Multiset.map_replicate,
      Multiset.prod_replicate, WD.card_eig, C_1]

private theorem eig_sum (x y : WD h) (σ : Weil h) : (x.lpSum y).eig σ = x.eig σ + y.eig σ := by
  rw [WD.eig, WD.eig, WD.eig, WD.charPol_lpSum, roots_mul]
  exact mul_ne_zero (WD.charPol_monic x σ).ne_zero (WD.charPol_monic y σ).ne_zero

private theorem tor_iff (x : WD h) :
    UpperTheory.GalStar.Tor x ↔ ∀ s t : ↥(Weil h), ∀ α ∈ x.eig ⁅s, t⁆, α = 1 :=
  forall_congr' fun s => forall_congr' fun t => pow_iff x ⁅s, t⁆

private theorem gd_sum (x y : WD h) : Gd (x.lpSum y) ↔ Gd x ∧ Gd y := by
  have ht : UpperTheory.GalStar.Tor (x.lpSum y) ↔ UpperTheory.GalStar.Tor x ∧ UpperTheory.GalStar.Tor y := by
    simp only [tor_iff, eig_sum, Multiset.mem_add]
    exact ⟨fun H => ⟨fun s t α hα => H s t α (Or.inl hα), fun s t α hα => H s t α (Or.inr hα)⟩,
      fun H s t α hα => hα.elim (H.1 s t α) (H.2 s t α)⟩
  unfold Gd
  rw [ht, WD.monomial_sum_iff]
  tauto

private theorem gd_tw (x : WD h) (t : ℝ) : Gd (x.lpTw t) ↔ Gd x := by
  have ht : UpperTheory.GalStar.Tor (x.lpTw t) ↔ UpperTheory.GalStar.Tor x := by
    simp only [tor_iff]
    refine forall_congr' fun s => forall_congr' fun u => ?_
    have hc : (unrChar h (qPow w t)) ⁅s, u⁆ = 1 := by
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    have he : (x.lpTw t).charPol ⁅s, u⁆ = x.charPol ⁅s, u⁆ := by
      rw [GlobalTheory.GalCut.AwayMono.charPol_lpTw, hc]
      simp
    rw [WD.eig, WD.eig, he]
  unfold Gd
  rw [ht, WD.monomial_twist_iff]

private theorem gd_zero : Gd (WD.lpZero (h := h)) := by
  refine ⟨(tor_iff _).2 fun s t α hα => ?_, ?_⟩
  · rw [WD.eig, GlobalTheory.LocLanglands.CuspExt.charPol_lpZero] at hα
    simp at hα
  · rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    rfl

private theorem gd_list (L : List (WD h)) : Gd (sumList L) ↔ ∀ x ∈ L, Gd x := by
  induction L with
  | nil => exact ⟨fun _ x hx => absurd hx (by simp), fun _ => gd_zero⟩
  | cons b L ih =>
    show Gd (WD.lpSum b (sumList L)) ↔ _
    rw [gd_sum, ih, List.forall_mem_cons]

private theorem deg_comm (s t : ↥(Weil h)) : deg ⁅s, t⁆ = 0 := by
  rw [commutatorElement_def]
  simp only [deg_mul, deg_inv]
  ring

private theorem gd_unr {x : WD h} (hx : x.unr) : Gd x := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ hx⟩
  have hi : ((⁅s, t⁆ : ↥(Weil h)) : G E Ω) ∈ Ine (F := E) A :=
    actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using deg_comm s t))
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  have h1 : a.ρ ⁅s, t⁆ = 1 := ((WD.unr_mk a).mp hx).2 ⟨_, hi⟩
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, h1, LinearMap.charpoly_one, WD.lpDim_mk]

end UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist

open UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist in
theorem UpperTheory.V.Z.Win.Gu.gdLaws :
    GdLaws := by
  intro E Ω _ _ _ _ _ A w h
  exact ⟨gd_sum, gd_tw, gd_list, fun _ => gd_unr⟩
