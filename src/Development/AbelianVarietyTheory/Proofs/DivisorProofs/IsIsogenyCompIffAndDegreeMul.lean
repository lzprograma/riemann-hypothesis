module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHomStatement
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

theorem GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    A.dim = B.dim → B.dim = C.dim →
      (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hAB hBC
  have hleft : (f ≫ g).hom.left = f.hom.left ≫ g.hom.left := by
    rw [comp_hom, Over.comp_left]
  have key : IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g := by
    constructor
    · rintro ⟨hfin, hsurj⟩
      have hs2 : Surjective (f.hom.left ≫ g.hom.left) := by rw [← hleft]; exact hsurj
      have hgs : Surjective g.hom.left := Surjective.of_comp f.hom.left g.hom.left
      have hgf : IsFinite g.hom.left := GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K B C g hBC hgs
      have hker : Finite (ptMap (f ≫ g)).ker := (GlobalTheory.T.isFinite_iff_finite_ker' K A C (f ≫ g)).1 hfin
      have hle : (ptMap f).ker ≤ (ptMap (f ≫ g)).ker := by
        intro x hx
        rw [MonoidHom.mem_ker] at hx ⊢
        have hx' : x ≫ f.hom = 1 := hx
        show x ≫ (f ≫ g).hom = 1
        rw [comp_hom, ← Category.assoc, hx', MonObj.one_comp]
      have hfk : Finite (ptMap f).ker :=
        Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      have hff : IsFinite f.hom.left := (GlobalTheory.T.isFinite_iff_finite_ker' K A B f).2 hfk
      exact ⟨⟨hff, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f hAB hff⟩, ⟨hgf, hgs⟩⟩
    · rintro ⟨hf, hg⟩
      exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g hf hg).1
  refine ⟨key, ?_⟩
  by_cases h : IsIsogeny f ∧ IsIsogeny g
  · exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g h.1 h.2).2
  · have h0 : deg (f ≫ g) = 0 := by
      unfold deg; rw [ite_eq_right (fun h' => h (key.1 h'))]
    rw [h0]
    rcases not_and_or.1 h with hf | hg
    · have : deg f = 0 := by unfold deg; rw [ite_eq_right hf]
      rw [this, zero_mul]
    · have : deg g = 0 := by unfold deg; rw [ite_eq_right hg]
      rw [this, mul_zero]
