module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmpleStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite, Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne\npublic import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmpleStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine\nimport Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV

theorem isAmpleCls_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left),
    IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  intro K _ A c d hc hd
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨M, hM, rfl⟩ := cls_surj d
  have hA : IsAmpleLB L := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 hc
  have hB : IsAmpleLB M := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A M hM).1 hd
  have hN : (tens L M).IsLB := isLB_tens hL hM
  have hT : IsAmpleLB (tens L M) := by
    refine hA.tensor hB hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hM)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hM, cls_div hN hL, cls_tens hL hM]
    abel
  rw [← cls_tens hL hM hN]
  exact (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A (tens L M) hN).2 hT

end GlobalTheory.AV
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmpleStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine\nimport Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem isAmpleCls_pull_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  intro K _ A B f d hf hd
  obtain ⟨L, hL, hrel, rfl⟩ := hd
  have hB : IsAmpleLB L := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K B L hL).1 ⟨L, hL, hrel, rfl⟩
  have hA : IsAmpleLB (L.pull f.hom.left) := hB.pull_of_isAffineHom f.hom.left
  have h := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A (L.pull f.hom.left) hA.isLB).2 hA
  rwa [cls_pull hL f.hom.left hA.isLB] at h

end GlobalTheory.AV.AbVar
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem neg_one_left_comp_self {K : Type} [Field K] (A : AbVar K) :
    (Hom.hom (-(𝟙 A))).left ≫ (Hom.hom (-(𝟙 A))).left = 𝟙 A.X.left := by
  have h : (-(𝟙 A)) ≫ (-(𝟙 A)) = 𝟙 A := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
  have h2 := congrArg (fun g : A ⟶ A => (Hom.hom g).left) h
  simpa only [comp_hom, Over.comp_left, id_hom, Over.id_left] using h2

theorem exists_symm_ample :
    ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c ∧ CechPic.pull (Hom.hom (-(𝟙 A))).left c = c := by
  intro K _ A
  obtain ⟨c₀, hc₀⟩ := _root_.GlobalTheory.AV.exists_isAmpleCls K A
  set f : A.X.left ⟶ A.X.left := (Hom.hom (-(𝟙 A))).left with hf
  have hff : f ≫ f = 𝟙 A.X.left := neg_one_left_comp_self A
  have hiso : IsIso f := ⟨⟨f, hff, hff⟩⟩
  have hfin : IsFinite (Hom.hom (-(𝟙 A))).left := by
    rw [← hf]; infer_instance
  refine ⟨c₀ + CechPic.pull f c₀, _root_.GlobalTheory.AV.isAmpleCls_add K A _ _ hc₀ (_root_.GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite K A A (-(𝟙 A)) c₀ hfin hc₀), ?_⟩
  rw [map_add (f := _), ← CechPic.pull_comp, hff, CechPic.pull_id, add_comm]

end GlobalTheory.AV.AbVar
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf =====
