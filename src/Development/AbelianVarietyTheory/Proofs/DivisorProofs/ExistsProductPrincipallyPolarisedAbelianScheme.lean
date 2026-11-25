module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumPol

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.PolProd

theorem exists_isPullback_restrict {X Y Z S : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (P : IsPullback p q f g) (h : Z ⟶ S) (hh : p ≫ f = h) (U : S.Opens) :
    ∃ (p' : (h ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme) (q' : (h ⁻¹ᵁ U).toScheme ⟶ (g ⁻¹ᵁ U).toScheme),
      p' ≫ (f ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ p ∧ q' ≫ (g ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ q ∧
        IsPullback p' q' (f ∣_ U) (g ∣_ U) := by
  have Hf := isPullback_morphismRestrict f U
  have Hg := isPullback_morphismRestrict g U
  have Hh := isPullback_morphismRestrict h U
  have w₁ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ p) ≫ f := by rw [Category.assoc, hh, Hh.w]
  have w₂ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ q) ≫ g := by rw [Category.assoc, ← P.w, hh, Hh.w]
  refine ⟨Hf.lift _ _ w₁, Hg.lift _ _ w₂, Hf.lift_snd _ _ _, Hg.lift_snd _ _ _, ?_⟩
  have A : IsPullback (Hf.lift _ _ w₁) (h ⁻¹ᵁ U).ι (f ⁻¹ᵁ U).ι p := by
    refine IsPullback.of_right ?_ (Hf.lift_snd _ _ _) Hf
    rw [Hf.lift_fst, hh]
    exact Hh
  have B := A.paste_vert P
  refine IsPullback.of_bot ?_ (by rw [Hf.lift_fst, Hg.lift_fst]) Hg
  rw [Hg.lift_snd, Hf.w]
  exact B

theorem relAmple_prod {S : Scheme.{0}} (A B : Over S) [IsProper A.hom] [IsProper B.hom] [IsProper (A ⊗ B).hom]
    {L : LB A.left} {M : LB B.left} {N : LB (A ⊗ B).left} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (e : cls N hN = pull (fst A B).left (cls L hL) + pull (snd A B).left (cls M hM))
    (aL : RelAmple A L) (aM : RelAmple B M) : RelAmple (A ⊗ B) N := by
  refine (relAmple_iff_isAmpleLB _ hN).2 fun U hU => ?_
  obtain ⟨p', q', hp, hq, H⟩ := exists_isPullback_restrict (p := (fst A B).left) (q := (snd A B).left)
    (f := A.hom) (g := B.hom) (IsPullback.of_hasPullback _ _) (A ⊗ B).hom (Over.w _) U
  have : IsAffine U := hU
  have h₀ := pull_isLB hN ((A ⊗ B).hom ⁻¹ᵁ U).ι
  have h₁ := pull_isLB (pull_isLB hL (A.hom ⁻¹ᵁ U).ι) p'
  have h₂ := pull_isLB (pull_isLB hM (B.hom ⁻¹ᵁ U).ι) q'
  refine IsAmpleLB.box ((relAmple_iff_isAmpleLB _ hL).1 aL U hU) ((relAmple_iff_isAmpleLB _ hM).1 aM U hU) h₀ H
    ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div h₀ h₁) h₂)).1 ?_)
  rw [cls_div (LB.isLB_div h₀ h₁) h₂, cls_div h₀ h₁, cls_pull hN, e, cls_pull (pull_isLB hL _), cls_pull hL,
    cls_pull (pull_isLB hM _), cls_pull hM, map_add, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, hp, hq]
  abel

end GlobalTheory.MumProd.SumPol
