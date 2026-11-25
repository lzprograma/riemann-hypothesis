module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X : Var F} {σ : F →+* ℂ}

theorem exists_ratVal_hom (y : CxPts X.str σ) :
    ∃ ψ : ((ratOf X).O (under y)).toSubring →+* ℂ, ∀ x : ((ratOf X).O (under y)).toSubring, ratVal (x : X.Fn) y = ψ x := by
  have h (x : ((ratOf X).O (under y)).toSubring) : ratVal (x : X.Fn) y = (ratOf X).val y.1 x := by
    obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 x.2).exists_fnOf
    rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
    refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
    rintro _ ⟨w, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]
  exact ⟨GlobalTheory.ZH.RatModel.valHom (M := ratOf X) y.1 _
    (GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf X) y.1 (IsLocalRing.closedPoint ℂ)), fun x => (h x).trans rfl⟩

theorem cInfAt_ratVal {κ : Type} [Fintype κ] {f : κ → X.Fn} {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a))
    {G : (κ → ℂ) → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) : CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hy g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hy)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, Set.univ, hW, isOpen_univ, trivial, hG.contDiffOn, ?_⟩
  filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
  congr 1
  funext a
  rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]

end GlobalTheory.GoodMetric
