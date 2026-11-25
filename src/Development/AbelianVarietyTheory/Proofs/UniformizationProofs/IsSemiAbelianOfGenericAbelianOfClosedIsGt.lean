module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU

namespace GlobalTheory

theorem isSemiAbelian_of_grpIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] [hc : IsCommMonObj G₂]
    (e : G₂ ≅ G₁) [IsMonHom e.hom] (h : IsSemiAbelian G₁) : IsSemiAbelian G₂ := by
  have hi : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have hw : G₂.hom = e.hom.left ≫ G₁.hom := (Over.w e.hom).symm
  have := h.smooth
  have := h.separated
  have := h.quasiCompact
  have hg := h.geomConnected
  refine ⟨hc, ?_, ?_, ?_, ?_, fun Ω _ _ q => ?_⟩
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩
    have hi' : IsIso ((Over.pullback q).map e.hom).left :=
      ((Over.pullback q ⋙ Over.forget _).mapIso e).isIso_hom
    have h1 : ConnectedSpace ((Over.pullback q).obj G₁).left := pullback_of_geometrically hg.1 K q
    exact (((Over.pullback q).map e.hom).left.homeomorph.connectedSpace_iff).2 h1
  · obtain ⟨E⟩ := h.fibres Ω q
    have : IsMonHom ((Over.pullback q).mapIso e).hom := inferInstanceAs (IsMonHom ((Over.pullback q).map e.hom))
    have : IsMonHom ((Over.pullback q).mapIso e).symm.hom :=
      inferInstanceAs (IsMonHom ((Over.pullback q).mapIso e).inv)
    exact ⟨torusExtOfIso ((Over.pullback q).mapIso e).symm E⟩

end GlobalTheory
