module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.ImmSep
open GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem eq_of_valHom_eq (x x' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valHom x U h = valHom x' U h') : x = x' := by
  have e₁ : x.appLE U ⊤ h = x'.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of R)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp R)) h
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec x' hU (isAffineOpen_top (Sp R)) h'
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem valHom_constFn {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    valHom x U h (constFn p U a) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (((x ≫ p).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) := by
  rw [← Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ le_top h]
  rfl

theorem eq_of_crd_eq : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x x' : Sp R ⟶ X) (v : J → R), x ≫ p = x' ≫ p → Crd H s x v → Crd H s x' v → x = x') := by
  intro k _ X p H J s J₀ _ hI R _ _ x x' v hp hx hx'
  have hm : x (IsLocalRing.closedPoint R) ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by
    rw [hI.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨hi₀, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have h := (top_le_iff x _).2 hi
  have hu : IsUnit (v i) := (crd_isUnit_iff i hx).2 h
  have h' := (crd_isUnit_iff i hx').1 hu
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i hi₀
  refine eq_of_valHom_eq x x' _ hA h h' (RingHom.eq_of_eqOn_set_dense hc ?_)
  rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
  · rw [valHom_constFn, valHom_constFn]
    simp only [hp]
  · have e := (crd_ratio hx (hr j) h).symm.trans (crd_ratio hx' (hr j) h')
    rw [valR_eq x _ h, valR_eq x' _ h'] at e
    exact hu.mul_right_cancel e

end GlobalTheory.ZH.ImmSep
end
