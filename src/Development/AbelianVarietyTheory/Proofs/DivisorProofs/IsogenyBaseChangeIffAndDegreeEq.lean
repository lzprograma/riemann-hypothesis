module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
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

theorem bcMap_isPullback (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L))) (bcMap L f).hom.left f.hom.left
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
  have h1 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)) =
      pullback.snd A.X.hom (spMap (algebraMap K L)) :=
    Over.w ((Over.pullback (spMap (algebraMap K L))).map f.hom)
  have h3 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left :=
    pullback.lift_fst _ _ _
  have h2 : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hout : IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L)))
      (((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)))
      (f.hom.left ≫ B.X.hom) (spMap (algebraMap K L)) := by
    rw [h1, h2]
    exact IsPullback.of_hasPullback A.X.hom (spMap (algebraMap K L))
  exact IsPullback.of_bot hout h3.symm (IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L)))

theorem isIsogeny_bcMap_iff_and_deg_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K)
    (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  intro K _ L _ _ A B f
  have := GlobalTheory.LevelMap.isFinite_descendsAlong_fpqc
  have sq := bcMap_isPullback K L f
  have hB := IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L))
  have hs : Surjective (spMap (algebraMap K L)) := GlobalTheory.LevelMap.surjective_spMap _
  have hf : Flat (spMap (algebraMap K L)) := GlobalTheory.LevelMap.flat_spMap _
  have hq : QuasiCompact (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact MorphismProperty.of_isPullback (P := @Surjective) hB.flip hs
    · exact MorphismProperty.of_isPullback (P := @Flat) hB.flip hf
    · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hB.flip hq
  have hiso : IsIsogeny (bcMap L f) ↔ IsIsogeny f :=
    and_congr (MorphismProperty.iff_of_isPullback (P := @IsFinite) sq.flip hQ)
      (MorphismProperty.iff_of_isPullback (P := @Surjective) sq.flip hQ)
  refine ⟨hiso, ?_⟩
  by_cases h : IsIsogeny f
  · obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B f h
    have : IsFinite f.hom.left := h.1
    have e : deg (bcMap L f) = (bcMap L f).hom.left.finrank (baseChange L B).origin := ite_eq_left (hiso.2 h)
    rw [e]
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ sq (baseChange L B).origin).trans (hrk _)
  · have e1 : deg (bcMap L f) = 0 := ite_eq_right (fun h' => h (hiso.1 h'))
    have e2 : deg f = 0 := ite_eq_right h
    rw [e1, e2]

end GlobalTheory.AV.AbVar
