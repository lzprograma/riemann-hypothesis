module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem gs_comp_stalkMap {Y Z Z' : Scheme.{0}} (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (U : Y.Opens)
    (h : r (ρ z) ∈ U) (a : Γ(Y, U)) :
    gs (ρ ≫ r) z U a = (ρ.stalkMap z).hom (gs r (ρ z) U a) := by
  rw [← gs_pull ρ r z U h a, gs_eq r (ρ z) U h, gs_eq ρ z (r ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ U) z h _).symm

theorem values_natural : ∀ (X Y Z Z' : Scheme.{0}) (L : LB X) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) ∧ (∀ s : LB.Sec (LB.LinComb L φ ε), sval s (ρ ≫ r) z J = (ρ.stalkMap z).hom (sval s r (ρ z) (fun ψ => J (ρ ≫ ψ)))) ∧ (∀ t : LB.Gen (LB.LinComb L φ ε), (val t (ρ ≫ r) z J).val = (ρ.stalkMap z).hom (val t r (ρ z) (fun ψ => J (ρ ≫ ψ))).val) ∧ ∀ c : Γ(Y, ⊤), gs (ρ ≫ r) z ⊤ c = (ρ.stalkMap z).hom (gs r (ρ z) ⊤ c) := by
  intro X Y Z Z' L K _ φ ε r ρ z J hJ
  have hJ' : Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) := fun ψ => hJ (ρ ≫ ψ)
  have hm := hJ'.mem φ r
  refine ⟨hJ', fun s => ?_, fun t => ?_, fun c => gs_comp_stalkMap r ρ z ⊤ trivial c⟩
  · rw [sval_of s (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact gs_comp_stalkMap r ρ z _ hm _
  · rw [val_of t (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact (gs_unit (ρ ≫ r) z _ hm _).symm.trans ((gs_comp_stalkMap r ρ z _ hm _).trans
      (congrArg (ρ.stalkMap z).hom (gs_unit r (ρ z) _ hm _)))

end GlobalTheory
