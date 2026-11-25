module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem exists_expandsF_and_nuGe_of_isComb : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → (∀ t : SecA A F k, ∃ σ, U.ExpandsF F k w₀ t σ) ∧ ∀ (I : Type) [Fintype I] (c : I → F) (s : I → SecA A F k) (t : SecA A F k) (q r : ℚ), IsComb s c t → (∀ i, (q : WithTop ℚ) ≤ v (c i)) → (∀ i σ, U.ExpandsF F k w₀ (s i) σ → NuGe D Q F v k σ r) → ∀ σ, U.ExpandsF F k w₀ t σ → NuGe D Q F v k σ (r + q) := by
  intro hL V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ hw k hk
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨h₁, -⟩ := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F k hk w₀ hw
  refine ⟨fun t => (h₁ t).exists, ?_⟩
  intro I _ c s t q r ht hq hs σ hσ
  choose Φ hΦ using fun i => (h₁ (s i)).exists
  have e := (GlobalTheory.TestFibre.isComb_iff_expandsF_sum hL V _ hA D A G hG U F k hk w₀ hw I s Φ c t hΦ).1 ht
  obtain rfl : σ = ∑ i, c i • Φ i := (h₁ t).unique hσ e
  refine Finset.sum_induction _ (fun x => NuGe D Q F v k x (r + q)) (fun a b ha hb => ?_) ?_ fun i _ => ?_
  · exact NuGe.add Q (s := a) (s' := b) (fun _ _ => rfl) ha hb
  · intro χ
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun j => by rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl⟩
  · exact NuGe.smul Q (hq i) ((isSmul_iff (c i) (Φ i) _).2 rfl) (hs i _ (hΦ i))

end GlobalTheory.ZH
