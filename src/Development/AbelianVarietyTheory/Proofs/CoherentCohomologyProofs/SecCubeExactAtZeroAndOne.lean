module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem secCube_exactAt_zero_and_one (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ]
    (D : κ → Y.Opens) (hD : ⨆ i, D i = ⊤) :
    (cubeComplex (secCube f M D)).ExactAt 0 ∧ (cubeComplex (secCube f M D)).ExactAt 1 := by
  let O : κ → Y.Opens := fun a => ⨅ i ∈ ({a} : Finset κ), D i
  have hOD (a : κ) : O a = D a := by simp [O]
  have hO (a : κ) : O a ≤ ⨅ i ∈ (∅ : Finset κ), D i :=
    iInf_le_iInf_of_subset D (Finset.empty_subset _)
  have hc : (⨅ i ∈ (∅ : Finset κ), D i) ≤ ⨆ a, O a := by
    simp only [hOD, hD, le_top]
  constructor
  · rw [cubeComplex_exactAt_zero_iff]
    intro s t h
    exact SecOnR.ext_of_cover f O hO hc fun a => congrFun h ⟨{a}, Finset.card_singleton a⟩
  · rw [cubeComplex_exactAt_one_iff]
    intro x
    constructor
    · intro hx
      have key (a b : κ) (hab : a < b) {W : Y.Opens} (ha : W ≤ O a) (hb : W ≤ O b) :
          SecOnR.restrict f M ha (x ⟨{a}, Finset.card_singleton a⟩) =
            SecOnR.restrict f M hb (x ⟨{b}, Finset.card_singleton b⟩) := by
        have e := Cube.d_one_apply_pair (secCube f M D) x hab
        rw [hx] at e
        have e' := (sub_eq_zero.1 e.symm).symm
        have hW : W ≤ ⨅ i ∈ ({a, b} : Finset κ), D i := by
          rw [hOD] at ha hb
          rw [Finset.iInf_insert, Finset.iInf_singleton]
          exact le_inf ha hb
        have e'' := congrArg (SecOnR.restrict f M hW) e'
        exact (SecOnR.restrict_restrict f _ _ _).symm.trans
          (e''.trans (SecOnR.restrict_restrict f _ _ _))
      obtain ⟨t, ht, -⟩ := SecOnR.existsUnique_glue f O hO hc
        (fun a => x ⟨{a}, Finset.card_singleton a⟩) fun a b => by
          rcases lt_trichotomy a b with h | rfl | h
          · exact key a b h _ _
          · rfl
          · exact (key b a h _ _).symm
      refine ⟨t, funext ?_⟩
      rintro ⟨s, hs⟩
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
      exact ht a
    · rintro ⟨t, rfl⟩
      have := Cube.d_zero_apply (secCube f M D) ((Cube.termZeroEquiv _).symm t)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact Cube.d_d _ 0 _

end GlobalTheory.AbLaw
