module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.LocSim

theorem exists_open_eq_of_torsion_point : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (σ σ' : 𝟙_ (Over S) ⟶ A), σ ^ n = 1 → σ' ^ n = 1 → ∀ (k : Type) [Field k] (y : Sp k ⟶ S), toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ' → ∃ V : S.Opens, Set.range y ⊆ (V : Set S) ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
  intro S A _ _ hA n hn σ σ' hσ hσ' k _ y hy
  haveI := hA.smooth
  haveI : FormallyUnramified (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := GlobalTheory.formallyUnramified_mulA S A n hn
  haveI : LocallyOfFiniteType (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := by
    have : LocallyOfFiniteType ((ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left ≫ A.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ A.hom
  have hab : σ.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left = σ'.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    show σ ≫ 𝟙 A ^ n = σ' ≫ 𝟙 A ^ n
    rw [MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, hσ, hσ']
  haveI := GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left hab
  refine ⟨(equalizer.ι σ.left σ'.left).opensRange, ?_, ?_⟩
  · have hy' : y ≫ σ.left = y ≫ σ'.left := by
      have h := congrArg CommaMorphism.left hy
      simp only [Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h
      exact h
    exact GlobalTheory.range_subset_range_equalizer_ι y hy'
  · rw [← cancel_epi (equalizer.ι σ.left σ'.left).isoOpensRange.hom, ← Category.assoc, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, equalizer.condition]

end GlobalTheory.UPel.LocSim
