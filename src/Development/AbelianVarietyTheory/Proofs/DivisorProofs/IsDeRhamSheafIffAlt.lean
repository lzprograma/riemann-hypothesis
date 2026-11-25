module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
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

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.ConjSeq

variable (p : ℕ) [Fact p.Prime]

abbrev frobR (R : Type) [CommRing R] (hR : (p : R) = 0) : R →+* R :=
  GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR

theorem frobR_apply (R : Type) [CommRing R] (hR : (p : R) = 0) (x : R) : frobR p R hR x = x ^ p :=
  congrArg (x ^ ·) (pow_one p)

theorem frob_sp (R : Type) [CommRing R] (hR : (p : R) = 0) (h : (p : Γ(Sp R, ⊤)) = 0) :
    GlobalTheory.VB.frob (Sp R) p h = spMap (frobR p R hR) :=
  GlobalTheory.SS.FrobField.absFrob_spec R p 1 Fact.out h _ fun _ ↦ rfl

theorem frob_comp_hom (R : Type) [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}} (f : X ⟶ Sp R)
    (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ f = f ≫ spMap (frobR p R hR) := by
  have h0 : (p : Γ(Sp R, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp R hR
  have hn : GlobalTheory.VB.frob X p h ≫ f = f ≫ GlobalTheory.VB.frob (Sp R) p h0 :=
    GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out h h0
  rw [hn, frob_sp p R hR h0]

theorem cast_left (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) :
    (p : Γ(A.left, ⊤)) = 0 :=
  GlobalTheory.SS.FrobField.cast_zero_of_hom A.hom (GlobalTheory.SS.FrobField.cast_zero_sp R hR)

theorem frobMor (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    (h : (p : Γ(A.left, ⊤)) = 0) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR) (spMap (frobR p R hR))
      (GlobalTheory.VB.frob A.left p h) := by
  refine { dp := isDPMorphism_of_eq_bot _ rfl _ _, base := ?_,
           w := frob_comp_hom p R hR A.hom h, mul := ?_ }
  · simp
  · intro T x y x₀ y₀ hx hy
    have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
    have hn (f : T.left ⟶ A.left) :
        GlobalTheory.VB.frob T.left p hT ≫ f = f ≫ GlobalTheory.VB.frob A.left p h :=
      GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out hT h
    let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
      Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
    have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
      simp only [hx, Over.comp_left, Over.homMk_left, j, hn])
    have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
      simp only [hy, Over.comp_left, Over.homMk_left, j, hn])
    subst ex ey
    rw [← MonObj.comp_mul]
    simp only [Over.comp_left, Over.homMk_left, j]
    exact hn (x * y).left

def frobDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    primDR A →ₛₗ[frobR p R hR] primDR A :=
  (frobMor p R hR A (cast_left p R hR A)).pull

def conjDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    Submodule R (primDR A) :=
  Submodule.span R (Set.range (frobDR p R hR A))

end GlobalTheory.ConjSeq

namespace GlobalTheory.DeRhamSheaf

open Limits

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

end GlobalTheory.DeRhamSheaf
