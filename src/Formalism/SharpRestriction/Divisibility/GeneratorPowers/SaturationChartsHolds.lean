module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds

-- ===== clump member: Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds =====
-- clump-header: {"m": "Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds", "h": "module\n\npublic import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsBasisOfSaturated\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.SaturatedCharts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Gen

variable {S : Scheme.{0}} {M : Over S} [MonObj M]

theorem comp_listProd {X Y : Over S} (f : X ⟶ Y) : ∀ {k : ℕ} (u : Fin k → (Y ⟶ M)),
    f ≫ (List.ofFn u).prod = (List.ofFn fun i => f ≫ u i).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.comp_one f
  | k + 1, u => by
    simp only [List.ofFn_succ, List.prod_cons, MonObj.comp_mul]
    rw [comp_listProd f (fun i => u i.succ)]

theorem listProd_comp {X : Over S} {N : Over S} [MonObj N] (g : M ⟶ N) [IsMonHom g] :
    ∀ {k : ℕ} (u : Fin k → (X ⟶ M)), (List.ofFn u).prod ≫ g = (List.ofFn fun i => u i ≫ g).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.one_comp g
  | k + 1, u => by
    simp only [List.ofFn_succ, List.prod_cons, MonObj.mul_comp]
    rw [listProd_comp g (fun i => u i.succ)]

end Gen

theorem fst_comp_jetTan {V : Type} [CommRing V] {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (TrivSqZeroExt.fstHom V V V).comp (jetTan (R := V) (m := 0) ℓ) = (jetAug : Jet V κ (0 + 1) →ₐ[V] V) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  by_cases h : i = ℓ <;>
    simp [jetTan, jetAug, liftJet, h, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk] <;>
    erw [Ideal.Quotient.lift_mk] <;> simp [h]

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
variable (t : SAB H (Sp V))

def toT (v : Sp (DualNumber V) ⟶ t.G.left) (h : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) ⟶ t.G :=
  Over.homMk v h

def eT : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) ⟶ tEpsG (𝟙 (Sp V)) :=
  Over.homMk (𝟙 _) (by simp)

def eT' : tEpsG (𝟙 (Sp V)) ⟶ ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) :=
  Over.homMk (𝟙 _) (by simp)

theorem prodPts_of_combAt {m : ℕ} (v : Fin m → (Sp (DualNumber V) ⟶ t.G.left))
    (hv : ∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (hc : IsCombAtG t (𝟙 (Sp V)) v a w) :
    toT t w hw = ReciprocityTheory.ChartRestriction.G.Chart.prodPts a (fun i => toT t (v i) (hv i)) := by
  obtain ⟨u, hu, hp⟩ := hc
  have h1 : toT t w hw = eT ≫ (List.ofFn u).prod := by
    apply Over.OverMorphism.ext
    simp only [toT, Over.homMk_left, Over.comp_left, eT, Category.id_comp]
    exact hp.symm
  rw [h1, comp_listProd]
  unfold ReciprocityTheory.ChartRestriction.G.Chart.prodPts
  congr 2
  funext i
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, eT, Over.homMk_left, Category.id_comp, hu i, toT]
  rfl

theorem combAt_of_prodPts {m : ℕ} (v : Fin m → (Sp (DualNumber V) ⟶ t.G.left))
    (hv : ∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (he : toT t w hw = ReciprocityTheory.ChartRestriction.G.Chart.prodPts a (fun i => toT t (v i) (hv i))) :
    IsCombAtG t (𝟙 (Sp V)) v a w := by
  refine ⟨fun i => eT' ≫ ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫ toT t (v i) (hv i),
    fun i => ?_, ?_⟩
  · simp only [Over.comp_left, eT', Over.homMk_left, Category.id_comp, toT]
    rfl
  · rw [← comp_listProd eT' (fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫
      toT t (v i) (hv i))]
    have he' : (List.ofFn fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫
        toT t (v i) (hv i)).prod = toT t w hw := he.symm
    rw [he']
    simp [eT', toT]

theorem chartTan_of (v : Sp (DualNumber V) ⟶ t.G.left) (h : IsTanAtG t (𝟙 (Sp V)) v) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t v ((h.1).trans (Category.comp_id _))) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom V V V).toRingHom) ≫ v =
    Spec.map (CommRingCat.ofHom (algebraMap V V)) ≫ η[t.G].left
  refine h.2.trans ?_
  show 𝟙 _ ≫ η[t.G].left = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem tanAt_of (v : Sp (DualNumber V) ⟶ t.G.left) (hv : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t v hv)) : IsTanAtG t (𝟙 (Sp V)) v := by
  refine ⟨hv.trans (Category.comp_id _).symm, ?_⟩
  have h' := congrArg CommaMorphism.left h
  refine h'.trans ?_
  show Spec.map (CommRingCat.ofHom (algebraMap V V)) ≫ η[t.G].left = 𝟙 _ ≫ η[t.G].left
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem isTan_iff' (w : epsOver V V ⟶ t.G) :
    IsTan w ↔ ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := V) (G := t.G) w :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg CommaMorphism.left h⟩

end Tan

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]


open ReciprocityTheory.ChartRestriction.G.Chart (tcoord tan_ext prodPts prodPts_tan) in
theorem saturation_charts_holds : ChartSaturated Xo c := by
  apply _root_.Formalism.L2.Pj.chart_saturated <;> assumption

end Main

end Formalism.L2.Pj.SaturatedCharts
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds =====
