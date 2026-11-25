module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_smul_mem_span_invariants_sup :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B] (N : Type)
      [AddCommGroup N] [Module B N] [DistribMulAction Γ N],
      (∀ (g : Γ) (b : B) (x : N), g • (b • x) = (g • b) • (g • x)) → ∀ q : Ideal B, q.IsPrime →
      (Nat.card (q.inertia Γ) : B) ∉ q →
      (∀ g ∈ q.inertia Γ, ∀ x : N, g • x - x ∈ q • (⊤ : Submodule B N)) →
      ∀ x : N, ∃ s : B, s ∉ q ∧
        s • x ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} ⊔ q • (⊤ : Submodule B N) := by
  intro Γ _ _ B _ _ N _ _ _ hsemi q hq hcard htriv x
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨n, c, d, s, hs, hsep⟩ := exists_sum_smul_separating_inertia Γ B q hq

  refine ⟨(Nat.card (q.inertia Γ) : B) * s, fun h => (hq.mem_or_mem h).elim hcard hs, ?_⟩

  have hinv : ∀ j, (∑ g : Γ, g • (c j • x)) ∈ {y : N | ∀ g : Γ, g • y = y} := by
    intro j h
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  obtain ⟨z, hzdef⟩ : ∃ z : N, z = ∑ j, d j • ∑ g : Γ, g • (c j • x) := ⟨_, rfl⟩
  have hz : z ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} := by
    rw [hzdef]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hinv j)))
  have hz' : z = ∑ g : Γ, (∑ j, d j * g • c j) • (g • x) := by
    rw [hzdef]
    simp only [Finset.smul_sum, hsemi, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : Nat.card (q.inertia Γ) = (Finset.univ.filter (fun g : Γ => g ∈ q.inertia Γ)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hsumI : ((Nat.card (q.inertia Γ) : B) * s) • x
      = ∑ g : Γ, if g ∈ q.inertia Γ then s • x else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, hc, ← Nat.cast_smul_eq_nsmul B, smul_smul]

  have hdiff : z - ((Nat.card (q.inertia Γ) : B) * s) • x ∈ q • (⊤ : Submodule B N) := by
    rw [hz', hsumI, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    by_cases hg : g ∈ q.inertia Γ
    · rw [ite_eq_left hg]
      have e : (∑ j, d j * g • c j) • (g • x) - s • x
          = ((∑ j, d j * g • c j) - s) • (g • x) + s • (g • x - x) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul ((hsep g).1 hg) Submodule.mem_top)
        (Submodule.smul_mem _ s (htriv g hg x))
    · rw [ite_eq_right hg, sub_zero]
      exact Submodule.smul_mem_smul ((hsep g).2 hg) Submodule.mem_top
  have key := Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hdiff)
  rwa [sub_sub_cancel] at key

end GlobalTheory
