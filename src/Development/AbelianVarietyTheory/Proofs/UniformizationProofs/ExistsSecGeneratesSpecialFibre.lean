module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace SpecialFibreGenerator

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_of_chart {L : LB X} (s : L.Sec) {a b : L.ι} {x : X} (ha : x ∈ L.U a)
    (hb : x ∈ X.basicOpen (s.f b)) : x ∈ X.basicOpen (s.f a) := by
  have h := congrArg X.basicOpen (s.compat a b)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have h₁ := X.basicOpen_res (s.f a) (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op
  have h₂ := X.basicOpen_res (s.f b) (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op
  have hab : x ∈ L.U a ⊓ L.U b := ⟨ha, X.basicOpen_le _ hb⟩
  exact (h₁.le (h.ge ⟨hab, h₂.ge ⟨hab, hb⟩⟩)).2

noncomputable def secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).Sec where
  f a := φ.appLE (L.U (a 0)) (LB.wchart L (fun _ ↦ φ) a) (LB.wchart_le L (fun _ ↦ φ) a 0) (s.f (a 0))
  compat a b := by
    have hle : LB.wchart L (fun _ : Fin 1 ↦ φ) a ⊓ LB.wchart L (fun _ : Fin 1 ↦ φ) b ≤
        φ ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
      inf_le_inf (LB.wchart_le L (fun _ ↦ φ) a 0) (LB.wchart_le L (fun _ ↦ φ) b 0)
    have h := congrArg (φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle) (s.compat (a 0) (b 0))
    rw [map_mul] at h
    have hg : ((LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).g a b).val =
        φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle (L.g (a 0) (b 0)).val := by
      simp only [LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    rw [hg]
    refine ((PrimeSection.res_appLE φ _ _ _).trans (PrimeSection.appLE_res φ _ _ _).symm).trans
      (h.trans (congrArg (_ * ·) ?_))
    exact (PrimeSection.appLE_res φ _ _ _).trans (PrimeSection.res_appLE φ _ _ _).symm

theorem mem_nonzeroLocus_secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) {y : Y} {a : L.ι}
    (h : φ y ∈ X.basicOpen (s.f a)) : y ∈ nonzeroLocus (secAlong s φ) := by
  refine Opens.mem_iSup.2 ⟨fun _ ↦ a, ?_⟩
  change y ∈ Y.basicOpen (φ.appLE _ _ _ _)
  exact (Scheme.basicOpen_appLE φ _ _ _ _).ge ⟨Set.mem_iInter.2 fun _ ↦ X.basicOpen_le _ h, h⟩

end SpecialFibreGenerator


end GlobalTheory
