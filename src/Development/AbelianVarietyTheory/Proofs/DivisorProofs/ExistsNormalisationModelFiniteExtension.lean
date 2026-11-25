module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem RatModel.stalkMap_pt_surjective {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (y : Sp Ω) : Function.Surjective (M.pt.stalkMap y).hom := by
  obtain rfl : y = closedPoint Ω := Subsingleton.elim _ _
  intro t
  obtain ⟨U, f, hU, hf⟩ := M.onto ((stalkClosedPointIso (CommRingCat.of Ω)).hom.hom t)
  have h : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt hU
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap M.pt U h
  refine ⟨(M.Z.presheaf.germ U _ ((GlobalTheory.Points.le_preimage_iff M.pt U).1 h)).hom f, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).1
  have e2 := congrArg (fun φ => φ.hom f) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_eq _ _ h] at hf
  rw [← hf, ← e2]
  rfl

theorem stalkMap_spMap_finite {K L : Type} [Field K] [Field L] (φ : K →+* L) (hφ : φ.Finite) (y : Sp L) :
    ((spMap φ).stalkMap y).hom.Finite := by
  obtain rfl : y = closedPoint L := Subsingleton.elim _ _
  have e := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom φ)
  have hc : (Scheme.stalkClosedPointTo (spMap φ)).hom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial).hom)
    have : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo (spMap φ)) =
        CommRingCat.ofHom φ := by
      rw [e, Iso.inv_hom_id_assoc]
    rw [← CommRingCat.hom_comp, Category.assoc, this]
    exact hφ
  have : (spMap φ).stalkMap (closedPoint L) =
      Scheme.stalkClosedPointTo (spMap φ) ≫ (stalkClosedPointIso (CommRingCat.of L)).inv := by
    rw [Scheme.stalkClosedPointTo, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of L)).inv).2) hc

end GlobalTheory.Poinc
