module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem isogeny_flat_finrank : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    A.dim = B.dim ∧ Flat f.hom.left ∧ 0 < deg f ∧ ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
  intro K _ A B f hf
  obtain ⟨hfin, hsurj⟩ := hf
  have hd := GlobalTheory.AV.DimLe.dim_le K A B f
  have hdim : A.dim = B.dim := le_antisymm (hd.1 hfin) (hd.2 hsurj)
  have hflat : Flat f.hom.left := by
    have hAg := A.smooth
    have hBg : SmoothOfRelativeDimension A.dim B.X.hom := hdim ▸ B.smooth
    have h := GlobalTheory.IsogenyQuasiInverse.flat_fibre A.X B.X A.dim A.ab B.ab hAg hBg f.hom K (𝟙 _)
    have e' : f.hom.left = ((Over.pullbackId (X := Sp K)).inv.app A.X).left ≫
        ((Over.pullback (𝟙 (Sp K))).map f.hom).left ≫
          ((Over.pullbackId (X := Sp K)).hom.app B.X).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      simp
    have i1 : IsIso ((Over.pullbackId (X := Sp K)).inv.app A.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).inv.app A.X)
    have i2 : IsIso ((Over.pullbackId (X := Sp K)).hom.app B.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).hom.app B.X)
    rw [e']
    exact Flat.comp _ _
  obtain ⟨hBint, hBnoeth, -⟩ := GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B
  have hdeg : deg f = f.hom.left.finrank B.origin := ite_eq_left ⟨hfin, hsurj⟩
  have hconst : ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
    intro y
    rw [hdeg]
    exact (Scheme.Hom.isLocallyConstant_finrank f.hom.left).apply_eq_of_preconnectedSpace y B.origin
  refine ⟨hdim, hflat, ?_, hconst⟩
  have h1 := (Scheme.Hom.one_le_finrank_iff_surjective f.hom.left).mpr hsurj B.origin
  rw [hdeg]
  exact h1

end GlobalTheory.AV.AbVar
