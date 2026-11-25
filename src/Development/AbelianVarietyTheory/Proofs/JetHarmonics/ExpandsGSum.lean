module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GroupExpansionLinear

open GlobalTheory.ExpansionLinear

theorem expandsG_sum : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k l : ℕ) (c : Fin l → F) (σ : Fin l → U.SecGF F k) (s : Fin l → Fam D.toPre F k) (σ' : U.SecGF F k), (∀ i, U.ExpandsG F k (σ i) (s i)) → (∀ jj, σ'.f jj = ∑ i, resTop _ (scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) * (σ i).f jj) → U.ExpandsG F k σ' (∑ i, c i • s i) := by
  intro R _ _ _ _ D A G _ _ U F _ _ k n c σ' s σ₀ ht h₀
  choose m d σ f hexp hG hB using ht
  let e : Fin (Fintype.card (Σ l, Fin (m l))) ≃ Σ l, Fin (m l) := (Fintype.equivFin _).symm
  refine ⟨_, fun i => c (e i).1 * d (e i).1 (e i).2, fun i => σ (e i).1 (e i).2, fun i => f (e i).1 (e i).2,
    fun i => hexp _ _, ?_, fun α => ?_⟩
  · exact secLin_comb _ _ _ _ _ _ _ σ' _ h₀ σ _ hG e _ (fun i => GlobalTheory.ExpansionLinear.scal_mul _ _ _)
  · exact secLin_comb _ _ _ _ _ _ (fun l => scal (fst (TF (R := R) F) D.toPre.P.A).left (c l))
      (fun l => (s l).s α) _ (fun j => fam_sum_f _ _ α j) (fun l i => f l i α) _ (fun l => hB l α) e _
      (fun i => GlobalTheory.ExpansionLinear.scal_mul _ _ _)

end GlobalTheory.GroupExpansionLinear
