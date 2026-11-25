module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.TrueGeo.SmallSec

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dite_eq_left h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem regAt_pow {x : Z} (hf : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = valR y U a := by
  have e : fnOf U h a = algebraMap _ Z.functionField (Z.presheaf.germ U (below y) hy a) :=
    (algebraMap_germ hy a).symm
  have ht : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y hy).ge
  have H := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  rw [e, valAt_algebraMap]
  first
  | rw [valR, dite_eq_left ht]
  refine H.trans ?_
  first
  | rfl

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  rw [ratVal, dite_eq_left hf]
  have he := hf.exists_fnOf.choose_spec.choose_spec.choose_spec
  conv_rhs => rw [← he]
  exact (valAt_fnOf hf.exists_fnOf.choose_spec.choose _ _).symm

end Val

section Fn

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

def fnMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fnMap_fnOf {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) : fnMap j hη (fnOf U h s) = fnOf (j ⁻¹ᵁ U) h' (j.app U s) := by
  show (X.presheaf.germ U _ h ≫ X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom s =
    (j.app U ≫ Y.presheaf.germ (j ⁻¹ᵁ U) (genericPoint Y) h').hom s
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem fnMap_algebraMap_eq_algebraMap_stalkMap (y : Y) (b : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField b) = algebraMap _ Y.functionField (j.stalkMap y b) := by
  have e1 := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint Y) y
    ((genericPoint_spec Y).specializes trivial) b
  simp only [RingHom.algebraMap_toAlgebra, fnMap]
  rw [← e1]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem exists_fnMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : RegAt y u) : ∃ t, RegAt (j y) t ∧ fnMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  exact ⟨algebraMap _ X.functionField b, ⟨b, rfl⟩, fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b⟩

theorem fnMap_surjective [IsPreimmersion j] : Function.Surjective (fnMap j hη) := fun u =>
  let ⟨t, _, ht⟩ := exists_fnMap_eq j hη (regAt_genericPoint u)
  ⟨t, ht⟩

theorem regAt_fnMap_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    RegAt y (fnMap j hη t) ↔ RegAt (j y) t := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fnMap_eq j hη h
    rwa [(fnMap j hη).injective e] at ht'
  · rintro ⟨b, rfl⟩
    exact ⟨_, (fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b).symm⟩

theorem valAt_fnMap {K : Type} [Field K] (y : Sp K ⟶ Y) {t : X.functionField}
    (h : RegAt (j (below y)) t) : valAt y (fnMap j hη t) = valAt (y ≫ j) t := by
  obtain ⟨b, rfl⟩ := h
  rw [fnMap_algebraMap_eq_algebraMap_stalkMap, valAt_algebraMap]
  refine Eq.trans ?_ (valAt_algebraMap (y := y ≫ j) b).symm
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

end Fn

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)

end Model

end GlobalTheory.TrueGeo.SmallSec
