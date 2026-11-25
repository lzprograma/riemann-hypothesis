module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetryHypExtendsSemiAbelianDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
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

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge.FormBC

theorem exists_grp {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  have abelian_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
      [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsAbelianScheme G)
      (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' := by
    have comm : IsCommMonObj G' := by
      have := hG.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨comm, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  obtain ⟨C, _, ψ, hψ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A (spMap (algebraMap R R'))
  let e : C ≅ Over.mk s' := Over.isoMk (hψ.1.isoIsPullback _ _ h) (by simp)
  let _ : GrpObj (Over.mk s') := GrpObj.ofIso e
  have : IsMonHom e.hom := inferInstance
  have hC := abelian_pull hA hψ
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ⟨inferInstance, abelian_pull hC (GlobalTheory.SymExtendDvr.isGrpPullback_of_iso e.symm),
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩

section Main

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
  {φ : X' ⟶ X}

end Main

end GlobalTheory.CompanionTheory.Hodge.FormBC
