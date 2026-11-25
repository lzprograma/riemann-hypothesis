module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.LyingOver.ExistsPosConstTypedTestFunctionBound, Development.AutomorphicArithmetic.LyingOver.TypedVectorsLeFixedOfFitsLevel, Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace

-- ===== clump member: Development.AutomorphicArithmetic.LyingOver.ExistsPosConstTypedTestFunctionBound =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.LyingOver.ExistsPosConstTypedTestFunctionBound", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor\nimport Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Separation.Connected\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.FiniteProductSplitting

noncomputable def glue {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {n : ℕ} (g : ∀ i, GL (Fin n) (R i)) :
    GL (Fin n) (∀ i, R i) where
  val := Matrix.of fun a b i => (g i : Matrix (Fin n) (Fin n) (R i)) a b
  inv := Matrix.of fun a b i => ((g i)⁻¹ : GL (Fin n) (R i)) a b
  val_inv := by
    ext a b i
    have := congrFun (congrFun (g i).mul_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl
  inv_val := by
    ext a b i
    have := congrFun (congrFun (g i).inv_mul a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl

theorem glue_cont {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] {n : ℕ} :
    Continuous (glue : (∀ i, GL (Fin n) (R i)) → GL (Fin n) (∀ i, R i)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_val.comp (continuous_apply i)).matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_coe_inv.comp (continuous_apply i)).matrix_elem a b

private theorem exists_ext {ι A : Type*} {X : A → Type*} (wi : ι → A) (hw : Function.Injective wi)
    (ψ : ∀ i, X (wi i)) (d : ∀ a, X a) :
    ∃ h : ∀ a, X a, (∀ i, h (wi i) = ψ i) ∧ ∀ a, a ∉ Set.range wi → h a = d a := by
  refine ⟨fun a => if ha : ∃ i, wi i = a then ha.choose_spec ▸ ψ ha.choose else d a, fun i => ?_,
    fun a ha => dite_eq_right ha⟩
  have key : ∀ j (hj : wi j = wi i), (hj ▸ ψ j : X (wi i)) = ψ i := by
    intro j hj
    obtain rfl := hw hj
    rfl
  have ha : ∃ j, wi j = wi i := ⟨i, rfl⟩
  simp only [dite_eq_left ha]
  exact key _ _

private theorem finprod_split {A M : Type*} [CommMonoid M] {r : ℕ} (wi : Fin r → A) (hw : Function.Injective wi)
    (X : A → M) (hX : (Function.mulSupport X).Finite) :
    ∏ᶠ u, X u = (∏ i, X (wi i)) * ∏ᶠ (u) (_ : u ∉ Set.range wi), X u := by
  have h := finprod_mem_inter_mul_diff' (f := X) (s := Set.univ) (Set.range wi)
    (hX.subset Set.inter_subset_right)
  rw [Set.univ_inter, finprod_mem_univ, finprod_mem_range hw, finprod_eq_prod_of_fintype] at h
  rw [← h]
  congr 1
  refine finprod_congr fun u => ?_
  simp only [Set.mem_diff, Set.mem_univ, true_and]

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem cmp_cont {v : Pl F} (w : PlacesOver E v) : Continuous (GM.cmp (n := n) w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem a b)
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_coe_inv.matrix_elem a b)

theorem liesOver_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

theorem finite_under (S : Set (Pl F)) (hS : S.Finite) :
    {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  refine (hS.biUnion fun v _ => Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  intro w hw
  exact Set.mem_biUnion hw ⟨⟨w, liesOver_under w⟩, rfl⟩

theorem iwCoset_zero (w : Pl E) :
    GM.iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w)) := by
  have hd : Cartan.diagPow (w.adicCompletion E) n (0 : Fin n → ℤ) = 1 := by
    apply Units.ext
    rw [Cartan.coe_diagPow]
    simp
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [hd, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [hd, mul_one, mul_one]⟩

theorem iw_test (w : Pl E) :
    IsLocallyConstant (((GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))).indicator (1 : Gw n w → ℂ)) ∧
      HasCompactSupport (((GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))).indicator (1 : Gw n w → ℂ)) := by
  have ho := GLnLocal.isOpen_iwahori (w.adicCompletion E) n
  have hc := GLnLocal.isCompact_iwahori (w.adicCompletion E) n
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))
  · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨_, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem prodFn_eq {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
    [Fintype (PlacesOver E v)] : GM.prodFn h = fun g => ∏ w, h w (GM.cmp w g) :=
  funext fun _ => finprod_eq_prod_of_fintype _

theorem prodFn_test {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
    (hc : ∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w)) :
    IsLocallyConstant (GM.prodFn h) ∧ HasCompactSupport (GM.prodFn h) := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  rw [prodFn_eq]
  constructor
  · have key : ∀ T : Finset (PlacesOver E v),
        IsLocallyConstant fun g : GL (Fin n) (CompletionsOver E v) => ∏ w ∈ T, h w (GM.cmp w g) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact IsLocallyConstant.const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((hc a).1.comp_continuous (cmp_cont a)).mul ih
    exact key _
  · haveI : T2Space (CompletionsOver E v) := Pi.t2Space
    haveI : T2Space (GL (Fin n) (CompletionsOver E v)) := Units.instT2Space
    haveI : R1Space (GL (Fin n) (CompletionsOver E v)) := T2Space.r1Space
    refine HasCompactSupport.intro ((isCompact_univ_pi fun w => (hc w).2.isCompact).image glue_cont) fun g hg => ?_
    by_contra hne
    refine hg ⟨fun w => GM.cmp w g, fun w _ => subset_tsupport _ ?_, ?_⟩
    · exact fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
    · exact Units.ext (Matrix.ext fun a b => rfl)

theorem unit_prod (v : Pl F) :
    (GM.prodFn fun w : PlacesOver E v => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E))).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ)) =
      (unitSet E n v).indicator 1 := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  funext g
  rw [GM.prodFn, finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ unitSet E n v
  · rw [Set.indicator_of_mem hg]
    exact Finset.prod_eq_one fun w _ => Set.indicator_of_mem (hg w) _
  · rw [Set.indicator_of_notMem hg]
    obtain ⟨w, hw⟩ := not_forall.1 hg
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _)

theorem iwFn_test {q : Pl F} (w₀ : PlacesOver E q) :
    IsLocallyConstant (GM.iwFn w₀ (0 : Fin n → ℤ)) ∧ HasCompactSupport (GM.iwFn w₀ (0 : Fin n → ℤ)) := by
  refine prodFn_test _ fun w => ?_
  rw [ite_self, iwCoset_zero]
  exact iw_test w.1

variable {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

noncomputable def dflt (T : Ty σ n q w₀) (w : Pl E) : Gw n w → ℂ :=
  (T.J w : Set (Gw n w)).indicator fun x => conj (T.χ w x)

theorem dflt_of_triv (T : Ty σ n q w₀) (w : Pl E) (h : T.χ w = 1) :
    dflt T w = (T.J w : Set (Gw n w)).indicator 1 := by
  unfold dflt
  rw [h]
  funext x
  by_cases hx : x ∈ (T.J w : Set (Gw n w))
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

private theorem sp_split (T : Ty σ n q w₀) {v : Pl F} (hv : v ∈ T.sp) : v ∈ T.S ∧ GM.Split E v :=
  Finset.mem_filter.1 hv

private theorem phi_eq (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ)
    (hF : T.Fits L ψ) (hq : GM.Split E q) (h : ∀ w : Pl E, Gw n w → ℂ)
    (h1 : ∀ v ∈ T.sp, h (T.mk' v).1 = ψ v)
    (h2 : ∀ w : Pl E, (∀ v ∈ T.sp, w ≠ (T.mk' v).1) → h w = dflt T w) (v : Pl F) :
    L.φ v = GM.prodFn fun u : PlacesOver E v => h u.1 := by
  have hother : ∀ (u : PlacesOver E v), v ∉ T.sp → h u.1 = dflt T u.1 := fun u hv => by
    refine h2 u.1 fun v' hv' e => hv ?_
    have : v' = v := by rw [← TY.under_of_over (T.mk' v'), ← e, TY.under_of_over u]
    rwa [← this]
  by_cases hsp : v ∈ T.sp
  · rw [(hF.split v hsp).1]
    congr 1
    funext u
    by_cases hu : u = T.mk' v
    · subst hu
      rw [Function.update_self, h1 v hsp]
    · rw [Function.update_of_ne hu, h2 u.1 fun v' hv' e => hu ?_,
        dflt_of_triv T u.1 (T.triv v (sp_split T hsp).2 u)]
      have : v' = v := by rw [← TY.under_of_over (T.mk' v'), ← e, TY.under_of_over u]
      subst this
      exact Subtype.ext e
  by_cases hS : v ∈ T.S
  · have hns : ¬ GM.Split E v := fun hs => hsp (Finset.mem_filter.2 ⟨hS, hs⟩)
    rw [hF.nonsplit v hS hns]
    congr 1
    funext u
    rw [hother u hsp]
    rfl
  by_cases hvq : v = q
  · subst hvq
    rw [L.at_q.1]
    unfold GM.iwFn
    congr 1
    funext u
    rw [hother u hsp, dflt_of_triv T u.1 (T.triv v hq u), ite_self, iwCoset_zero, T.at_q u]
  · have hvS : v ∉ L.S := by rw [hF.S_eq]; exact hS
    rw [(L.off v hvS hvq).1, ← unit_prod v]
    congr 1
    funext u
    have hu := T.off u.1 (by rw [TY.under_of_over]; exact hS) (by rw [TY.under_of_over]; exact hvq)
    rw [hother u hsp, dflt_of_triv T u.1 hu.2, hu.1]

end Main

end UpperTheory.FiniteProductSplitting

open UpperTheory.FiniteProductSplitting in
theorem UpperTheory.exists_pos_const_typed_test_function_bound :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
        ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (aE : TI E n)
          (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ T : Ty σ n q w₀,
        ∃ κ : ℝ, 0 < κ ∧ ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
          ∀ (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ v, v ∈ T.sp ↔ v ∈ Set.range p) →
          ∀ [∀ i, MeasurableSpace (Gw n (T.mk' (p i)).1)] [∀ i, BorelSpace (Gw n (T.mk' (p i)).1)]
            (mm : ∀ i, Measure (Gw n (T.mk' (p i)).1)), (∀ i, (mm i).IsHaarMeasure ∧ mm i (T.J (T.mk' (p i)).1) = 1) →
          ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm i) (ψ (p i)) (B i)) →
          ∀ g : TG E n, (∀ x, g x = avg (tensE (GM.onInf aE) L.φ) x) →
            Rop μ g = (κ : ℂ) • (Oinf μ νE aE ∘L (List.ofFn B).prod ∘L prj (T.typed μ)) := by
  intro F E _ _ _ _ _ σ n hn μ _ νE _ aE q w₀ hq T
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ ((insert q T.S : Finset (Pl F)) : Set (Pl F))}.Finite :=
    finite_under _ (Finset.finite_toSet _)
  have hcof : ∀ᶠ w : Pl E in Filter.cofinite,
      w.under (𝓞 F) ∉ T.S ∧ w.under (𝓞 F) ≠ q := by
    refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_and_or, not_not] at hw
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    tauto
  obtain ⟨κ, hκ, H⟩ := tensFactor E n hn μ νE T.J T.χ (fun w => ⟨T.co w, T.chr w⟩)
    (hcof.mono fun w hw => T.off w hw.1 hw.2)
  refine ⟨κ, hκ, ?_⟩
  intro L ψ hF r p hp hsp _ _ mm hmm B hB g hg
  have hpS : ∀ i, p i ∈ T.sp := fun i => (hsp _).2 ⟨i, rfl⟩
  have hwi : Function.Injective fun i => (T.mk' (p i)).1 := fun i j e => hp (by
    have e' : (T.mk' (p i)).1 = (T.mk' (p j)).1 := e
    rw [← TY.under_of_over (T.mk' (p i)), e', TY.under_of_over])
  obtain ⟨h, hh1, hh2⟩ := exists_ext (X := fun w : Pl E => Gw n w → ℂ) (fun i => (T.mk' (p i)).1) hwi
    (fun i => ψ (p i)) (dflt T)
  have h1 : ∀ v ∈ T.sp, h (T.mk' v).1 = ψ v := fun v hv => by
    obtain ⟨i, rfl⟩ := (hsp v).1 hv
    exact hh1 i
  have h2 : ∀ w : Pl E, (∀ v ∈ T.sp, w ≠ (T.mk' v).1) → h w = dflt T w := fun w hw =>
    hh2 w fun ⟨i, e⟩ => hw _ (hpS i) e.symm
  have hφ := phi_eq T L ψ hF hq h h1 h2
  have hint : ∀ᶠ w : Pl E in Filter.cofinite,
      h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator 1 := by
    refine hcof.mono fun w hw => ?_
    have hu := T.off w hw.1 hw.2
    have hne : ∀ v ∈ T.sp, w ≠ (T.mk' v).1 := fun v hv e => hw.1 (by
      rw [e, TY.under_of_over]; exact (sp_split T hv).1)
    rw [h2 w hne, dflt_of_triv T w hu.2, hu.1]
  obtain ⟨e, -, he, ht⟩ := GM.avgE F E n hn (insert q L.S) aE L.φ (fun v hv => by
      rcases Finset.mem_insert.1 hv with hvq | hv
      · rw [hvq, L.at_q.1]; exact iwFn_test w₀
      · exact ⟨(L.test v hv).1, (L.test v hv).2.1⟩)
    (fun v hv => (L.off v (fun h => hv (Finset.mem_insert_of_mem h))
      (fun h => hv (by rw [h]; exact Finset.mem_insert_self _ _))).1)
  have hgt : g = tens aE e := by
    ext x
    rw [hg, ht]
  have heform : ∀ x, e x = (∏ i, ψ (p i) (finAt (T.mk' (p i)).1 (finEmb E n x))) *
      ∏ᶠ u ∉ Set.range (fun i => (T.mk' (p i)).1), (T.J u : Set (Gw n u)).indicator (fun g => conj (T.χ u g)) (finAt u (finEmb E n x)) := by
    intro x
    have e1 : e x = ∏ᶠ w, h w (finAt w (finEmb E n x)) := by
      rw [he x, ← UpperTheory.ConvolutionTheory.Tf.tensEProd F E n h hint (finEmb E n x)]
      exact finprod_congr fun v => by rw [hφ v]
    have hsupp : (Function.mulSupport fun w : Pl E => h w (finAt w (finEmb E n x))).Finite := by
      have hev : ∀ᶠ w : Pl E in Filter.cofinite, h w (finAt w (finEmb E n x)) = 1 := by
        filter_upwards [hint, AdelicGLn.eventually_mem_integralGL E n (finEmb E n x)] with w a1 a2
        rw [a1, Set.indicator_of_mem (by exact a2)]
        rfl
      exact Filter.eventually_cofinite.1 hev
    rw [e1, finprod_split _ hwi _ hsupp]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [hh1 i]
    · refine finprod_congr fun u => finprod_congr fun hu => ?_
      rw [hh2 u hu]
      rfl
  have main := H aE r (fun i => (T.mk' (p i)).1) hwi mm hmm (fun i => ψ (p i)) B (fun i => ⟨(hF.test _ (hpS i)).1,
    fun u hu g' => by
      have hχ := T.triv (p i) (sp_split T (hpS i)).2 (T.mk' (p i))
      rw [((hF.test _ (hpS i)).2 u hu g').2, hχ]
      simp, hB i⟩) e heform
  rw [hgt]
  exact main
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.LyingOver.ExistsPosConstTypedTestFunctionBound =====

-- ===== clump member: Development.AutomorphicArithmetic.LyingOver.TypedVectorsLeFixedOfFitsLevel =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.LyingOver.TypedVectorsLeFixedOfFitsLevel", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate Classical InnerProductSpace

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem chr_one {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ) : χ 1 = 1 := by
  have h1 := h.2.2 1 J.one_mem 1 J.one_mem
  have h2 : χ 1 ≠ 0 := fun h0 => by
    have := h.2.1 1 J.one_mem
    rw [h0] at this
    simp at this
  rw [mul_one] at h1
  exact (mul_eq_left₀ h2).1 h1.symm

private theorem at_place {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q} (hq : GM.Split E q)
    (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) {ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ} (hF : T.Fits L ψ) (v : Pl F)
    (x : GL (Fin n) (CompletionsOver E v)) (hx : x ∈ L.UE v) :
    (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) ∧
      ∏ᶠ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x) = 1 := by
  have easy : (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) → (∀ u : PlacesOver E v, T.χ u.1 = 1) →
      (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) ∧
      ∏ᶠ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x) = 1 := fun h1 h2 => by
    refine ⟨h1, ?_⟩
    rw [finprod_eq_prod_of_fintype]
    refine Finset.prod_eq_one fun u _ => ?_
    rw [Set.indicator_of_mem (by exact h1 u), h2 u]
    rfl
  by_cases hvq : v = q
  · subst hvq
    refine easy (fun u => ?_) (T.triv v hq)
    rw [T.at_q u]
    exact (L.at_q.2.2.1 x).1 hx u
  by_cases hvS : v ∈ T.S
  · by_cases hs : GM.Split E v
    · have hsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hvS, hs⟩
      exact easy (((hF.split v hsp).2 x).1 hx) (T.triv v hs)
    · have hvL : v ∈ L.S := hF.S_eq ▸ hvS
      have hinv := (L.inv v hvL).1 x hx 1
      rw [mul_one, hF.nonsplit v hvS hs] at hinv
      unfold GM.prodFn at hinv
      rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype] at hinv
      have h1 : ∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (fun y => conj (T.χ u.1 y)) (GM.cmp u 1) = 1 := by
        refine Finset.prod_eq_one fun u _ => ?_
        rw [map_one, Set.indicator_of_mem (by exact one_mem _), chr_one (T.chr u.1)]
        simp
      rw [h1] at hinv
      have hm : ∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1 := fun u => by
        by_contra hc
        have : ∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (fun y => conj (T.χ u.1 y)) (GM.cmp u x) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ u) (Set.indicator_of_notMem (by exact hc) _)
        rw [this] at hinv
        exact zero_ne_one hinv
      refine ⟨hm, ?_⟩
      rw [finprod_eq_prod_of_fintype]
      have h2 : conj (∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x)) = 1 := by
        rw [map_prod, ← hinv]
        refine Finset.prod_congr rfl fun u _ => ?_
        rw [Set.indicator_of_mem (by exact hm u)]
        exact (Set.indicator_of_mem (s := (T.J u.1 : Set (Gw n u.1))) (hm u) fun y => conj (T.χ u.1 y)).symm
      have h3 := congrArg (starRingEnd ℂ) h2
      simpa using h3
  · have hvL : v ∉ L.S := fun h => hvS (hF.S_eq ▸ h)
    have hu : x ∈ unitSet E n v := by
      rw [← (L.off v hvL hvq).2.2.1]
      exact hx
    have hoff : ∀ u : PlacesOver E v, T.J u.1 = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ T.χ u.1 = 1 := fun u =>
      T.off u.1 (by rwa [TY.under_of_over]) (by rwa [TY.under_of_over])
    refine easy (fun u => ?_) fun u => (hoff u).2
    rw [(hoff u).1]
    exact hu u

end SlopeTestRemainingChoices

theorem UpperTheory.typed_vectors_le_fixed_of_fits_level :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ)
        (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
        (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
        T.typed μ ≤ fixF μ (GM.levE L.UE) := by
  intro F E _ _ _ _ _ σ n q w₀ hq μ _ T L ψ hF f hf
  have hfw : ∀ w, f ∈ eigL μ w (T.J w) (T.χ w) := (Submodule.mem_iInf _).1 hf
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).2.1 f).2 fun g hg => ?_
  have hX : ∀ v : Pl F, mapGL n (atFin v) (finEmb E n g) ∈ L.UE v := fun v => Subgroup.mem_iInf.1 hg v
  have hloc := fun v : Pl F => at_place hq T L hF v _ (hX v)
  have hJ : ∀ w : Pl E, finAt w (finEmb E n g) ∈ T.J w := fun w => by
    have := (hloc (w.under (𝓞 F))).1 ⟨w, ⟨rfl⟩⟩
    rwa [TY.cmp_atFin] at this
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
    refine ((insert q T.S).finite_toSet.biUnion fun v _ => TY.finite_over (E := E) v).subset ?_
    intro w hw
    exact Set.mem_biUnion (x := w.under (𝓞 F)) hw rfl
  set P : Finset (Pl E) := hfin.toFinset with hPdef
  have hP : ∀ w ∉ P, T.J w = GLnLocal.integralGL (w.adicCompletion E) n ∧ T.χ w = 1 := fun w hw => by
    have : w.under (𝓞 F) ∉ insert q T.S := fun h => hw (hfin.mem_toFinset.2 h)
    rw [Finset.mem_insert, not_or] at this
    exact T.off w this.2 this.1
  have hr := TY.rho_typed μ T.J T.χ f hfw P hP P g (fun w _ => hJ w) (fun w h1 h2 => absurd h1 h2)
    (fun w hw => by rw [← (hP w hw).1]; exact hJ w)
  have hone : ∏ w ∈ P, T.χ w (finAt w (finEmb E n g)) = 1 := by
    have ht := UpperTheory.ConvolutionTheory.Tf.tensEProd F E n (fun w => (T.J w : Set (Gw n w)).indicator (T.χ w))
      (by
        refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
        by_contra hc
        apply hw
        have hwP : w ∉ P := fun h => hc (hfin.mem_toFinset.1 h)
        obtain ⟨e1, e2⟩ := hP w hwP
        simp only [e1, e2]) (finEmb E n g)
    have hl : ∀ v : Pl F, GM.prodFn (v := v) (fun w => (T.J w.1 : Set (Gw n w.1)).indicator (T.χ w.1))
        (mapGL n (atFin v) (finEmb E n g)) = 1 := fun v => (hloc v).2
    simp only [hl, finprod_one] at ht
    rw [finprod_eq_prod_of_mulSupport_subset (s := P)] at ht
    · rw [ht]
      exact Finset.prod_congr rfl fun w _ => (Set.indicator_of_mem (by exact hJ w) _).symm
    · intro w hw
      by_contra hc
      apply hw
      obtain ⟨e1, e2⟩ := hP w (by simpa using hc)
      simp only [Set.indicator_of_mem (show finAt w (finEmb E n g) ∈ (T.J w : Set (Gw n w)) from hJ w), e2]
      rfl
  rw [hr, hone, one_smul]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.LyingOver.TypedVectorsLeFixedOfFitsLevel =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY\npublic import Development.AutomorphicArithmetic.LyingOver.ExistsPosConstTypedTestFunctionBound\npublic import Development.AutomorphicArithmetic.LyingOver.TypedVectorsLeFixedOfFitsLevel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate Classical InnerProductSpace
open UpperTheory.ConvolutionTheory.L1.TY (prj_mem prj_self mem_eigIn prj_eigIn_comp_prj trace_sm
  rhoL_comm arch_comm oloc_comm oloc_fix oinf_congr)
namespace UpperTheory.ConvolutionTheory.L1.SideTr

private theorem alg {R : Type} [Ring R] [Algebra ℂ R] (PX P PZ A Oa Ui Bp U : R) (k x : ℂ)
    (h1 : PX * P = PZ) (h2 : P * PX = PZ) (h3 : PX * A = x • PX) (h4 : Ui * A = A * Ui)
    (h5 : Oa * (Bp * P) = A * (Bp * P)) (h6 : (Ui * Bp) * P = P * ((Ui * Bp) * P)) (h7 : P * U = U * P) :
    PX * ((Ui * ((k • (Oa * (Bp * P))) * U)) * PX) = (k * x) • (PZ * (((Ui * Bp) * U) * PZ)) := by
  have e2 : PX * (Ui * Bp * P * U) * PX = PZ * (Ui * Bp * U * PZ) := by
    calc PX * (Ui * Bp * P * U) * PX = PX * (P * (Ui * Bp * P)) * U * PX := by
          rw [← h6]; simp only [mul_assoc]
      _ = PZ * (Ui * Bp) * (P * U) * PX := by rw [← h1]; simp only [mul_assoc]
      _ = PZ * (Ui * Bp) * U * (P * PX) := by rw [h7]; simp only [mul_assoc]
      _ = PZ * (Ui * Bp * U * PZ) := by rw [h2]; simp only [mul_assoc]
  have e1 : Ui * ((k • (Oa * (Bp * P))) * U) = k • (A * (Ui * Bp * P * U)) := by
    rw [h5, smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [← mul_assoc]
    rw [h4]
  rw [e1, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc, h3, smul_mul_assoc, smul_mul_assoc, smul_smul, ← e2,
    mul_assoc PX]

section Ty
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q} (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]

private theorem mem_typed (T : Ty σ n q w₀) {v : LL μ} :
    v ∈ T.typed μ ↔ ∀ w, ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
  simp only [Ty.typed, Submodule.mem_iInf, _root_.UpperTheory.ConvolutionTheory.L1.TY.mem_eigL]

private theorem typed_closed (T : Ty σ n q w₀) : IsClosed (T.typed μ : Set (LL μ)) := by
  simp only [Ty.typed, Submodule.coe_iInf]
  exact isClosed_iInter fun w => (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w _ _ (T.co w) (T.chr w)).1

private theorem comm_typed (T : Ty σ n q w₀) (R : LL μ →L[ℂ] LL μ) (hR : ∀ w g, Commute R (rhoL μ w g)) (v : LL μ)
    (hv : v ∈ T.typed μ) : R v ∈ T.typed μ := by
  rw [mem_typed] at hv ⊢
  intro w x hx
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR w x).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [← this, hv w x hx, map_smul]

private theorem typed_step (T : Ty σ n q w₀) (Bo : LL μ →L[ℂ] LL μ) (w₁ : Pl E)
    (hfix : ∀ v, Bo v ∈ fixL μ w₁ (T.J w₁)) (hχ : T.χ w₁ = 1)
    (hc : ∀ w, w ≠ w₁ → ∀ g, Commute Bo (rhoL μ w g)) (v : LL μ) (hv : v ∈ T.typed μ) : Bo v ∈ T.typed μ := by
  rw [mem_typed] at hv ⊢
  intro w x hx
  by_cases h : w = w₁
  · subst h
    have hch : IsChr (T.J w) 1 := hχ ▸ T.chr w
    have h1 := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) hch).2.1
    have h2 : Bo v ∈ eigL μ w (T.J w) 1 := by rw [h1]; exact hfix v
    rw [hχ]
    exact (_root_.UpperTheory.ConvolutionTheory.L1.TY.mem_eigL μ).1 h2 x hx
  · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hc w h x).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [← this, hv w x hx, map_smul]

end Ty

end UpperTheory.ConvolutionTheory.L1.SideTr


open UpperTheory.ConvolutionTheory.L1.SideTr in
theorem UpperTheory.ConvolutionTheory.L1.sideTrace :
    UpperTheory.ConvolutionTheory.L1.SideTrace := by
  intro F E _ _ _ _ _ _ σ hσ m n hfr hn μ _ θ hθ D s hs hsl νE _ νF _ b a aE aF hA q w₀ hq T V hV hVU hR y hy
  obtain ⟨c₀, hc₀, hB⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hσ m n hfr hn μ θ hθ D s hs hsl νE νF b a aE aF hA q w₀ hq T V hV hVU hR).2 y hy
  obtain ⟨κ, hκ, hK⟩ := UpperTheory.exists_pos_const_typed_test_function_bound F E σ n hn μ νE aE q w₀ hq T
  have hx : (0 : ℝ) < y ^ (m + 1) := pow_pos hy _
  refine ⟨(κ : ℂ) * ((y ^ (m + 1) : ℝ) : ℂ) * c₀, mul_ne_zero (mul_ne_zero (by exact_mod_cast hκ.ne') (by exact_mod_cast hx.ne')) hc₀, ?_⟩
  intro L ψ hF ν l 𝔢 hE r p hp hpr _ _ mm hmm B hBo j
  obtain ⟨hν, ha, -, hU, hg, hUq⟩ := hE
  have hKg := hK L ψ hF r p hp hpr mm hmm B hBo 𝔢.g hg
  have hle : T.typed μ ≤ fixF μ (GM.levE L.UE) := UpperTheory.typed_vectors_le_fixed_of_fits_level F E σ n q w₀ hq μ T L ψ hF
  have hcp := UpperTheory.ConvolutionTheory.Tf.commPrj E n μ (GM.levE L.UE)
  have hAeq : 𝔢.toAmp.A = Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE)) := by
    show Oinf μ 𝔢.ν 𝔢.a₀ ∘L prj (fixF μ 𝔢.U) = _
    rw [ha, hU, oinf_congr μ hν]
  have hpos : 0 ≤ Oinf μ νE aE := by
    have := 𝔢.pos
    rwa [ha, oinf_congr μ hν] at this
  have hOsa : ContinuousLinearMap.adjoint (Oinf μ νE aE) = Oinf μ νE aE :=
    (IsSelfAdjoint.of_nonneg hpos).adjoint_eq
  have hOF : ∀ h, Commute (Oinf μ νE aE) (rhoF μ h) := fun h =>
    (UpperTheory.ConvolutionTheory.Tf.opAlg E n μ νE MeasureTheory.Measure.haar).2.2.2.2.2.2.2.2 aE h
  have hOT : ∀ v ∈ T.typed μ, Oinf μ νE aE v ∈ T.typed μ :=
    comm_typed μ T _ fun w g => hOF _
  have hOFx : ∀ v ∈ fixF μ (GM.levE L.UE), Oinf μ νE aE v ∈ fixF μ (GM.levE L.UE) := by
    intro v hv
    refine (hcp.2.1 _).2 fun u hu => ?_
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hOF u).eq
    simp only [ContinuousLinearMap.mul_apply, (hcp.2.1 v).1 hv u hu] at this
    exact this.symm
  have hVc : IsClosed (V : Set (LL μ)) := IsSummandOf.closed hV
  have hVT : ∀ v ∈ T.typed μ, prj V v ∈ T.typed μ := by
    refine comm_typed μ T _ fun w g => ?_
    exact ((UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.1 _ V hVc (IsSummandOf.inv hV)).symm
  obtain ⟨k1, k2, k3⟩ := prj_eigIn_comp_prj (T.typed μ) (fixF μ (GM.levE L.UE)) V (typed_closed μ T) hcp.1 hVc hle (Oinf μ νE aE) hOsa hOT hOFx hVT (y ^ (m + 1))
  have hθP : Commute θ.U (prj (T.typed μ)) := by
    have h0 := (UpperTheory.ConvolutionTheory.L1.twistPerm F E σ hσ m n μ θ hθ).2.2 q w₀ T ∅
    have h1 : (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ (∅ : Set (Pl F))), eigL μ w (T.J w) (T.χ w)) = T.typed μ := by
      simp [Ty.typed]
    rwa [h1] at h0

  let Good : (LL μ →L[ℂ] LL μ) → Prop := fun O => (∀ v ∈ T.typed μ, O v ∈ T.typed μ) ∧
    (∀ g, Commute O (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n g))) ∧ (∀ w ∉ T.marked, ∀ g, Commute O (rhoL μ w g))
  have hGone : Good 1 := ⟨fun v hv => hv, fun g => Commute.one_left _, fun w _ g => Commute.one_left _⟩
  have hGmul : ∀ O₁ O₂, Good O₁ → Good O₂ → Good (O₁ * O₂) := fun O₁ O₂ h₁ h₂ =>
    ⟨fun v hv => h₁.1 _ (h₂.1 v hv), fun g => (h₁.2.1 g).mul_left (h₂.2.1 g),
      fun w hw g => (h₁.2.2 w hw g).mul_left (h₂.2.2 w hw g)⟩
  have hBG : Good (List.ofFn B).prod := by
    refine List.prod_induction _ hGmul hGone fun O hO => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    haveI := (hmm i).1
    have hsp : p i ∈ T.sp := (hpr _).2 ⟨i, rfl⟩
    have hspl : GM.Split E (p i) := (Finset.mem_filter.1 hsp).2
    have ht := (hF.test (p i) hsp).2
    have hne : ∀ w ∉ T.marked, w ≠ (T.mk' (p i)).1 := fun w hw h => hw (Or.inr ⟨p i, hsp, h⟩)
    refine ⟨typed_step μ T (B i) _ (oloc_fix μ (hBo i) _ fun u hu g => (ht u hu g).1) (T.triv _ hspl _) (fun w hw g => ?_),
      fun g => ?_, fun w hw g => ?_⟩
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ hw g g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => arch_comm μ g _ g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUG : Good (Uiw μ w₀.1 ν) := by
    have hI : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
    have hco := T.co w₀.1
    rw [hI] at hco
    have hh := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w₀.1 (GLnLocal.iwahori _ n) (Cartan.diagPow _ n ν) hco.2 hco.1
    have hne : ∀ w ∉ T.marked, w ≠ w₀.1 := fun w hw h => hw (Or.inl h)
    refine ⟨typed_step μ T _ w₀.1 (fun v => ?_) (T.triv q hq w₀) (fun w hw g => ?_), fun g => ?_, fun w hw g => ?_⟩
    · rw [hI]; exact hh.2.1 v
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ hw g g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => arch_comm μ g _ g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUjG : Good (Uiw μ w₀.1 ν ^ j) := by
    induction j with
    | zero => simpa using hGone
    | succ k ih => rw [pow_succ]; exact hGmul _ _ ih hUG
  have hCG : Good (Uiw μ w₀.1 ν ^ j * (List.ofFn B).prod) := hGmul _ _ hUjG hBG
  have hal := alg (prj (eigIn V (Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE))) (y ^ (m + 1)))) (prj (T.typed μ))
    (prj (eigIn (V ⊓ T.typed μ) (Oinf μ νE aE) (y ^ (m + 1)))) (Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE))) (Oinf μ νE aE)
    (Uiw μ w₀.1 ν ^ j) (List.ofFn B).prod θ.U (κ : ℂ) ((y ^ (m + 1) : ℝ) : ℂ) k1 k2 k3
    (by
      have := ((𝔢.Uq_amp 0).pow_left j).eq
      rwa [hUq, hAeq] at this)
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      show Oinf μ νE aE ((List.ofFn B).prod (prj (T.typed μ) v)) =
        Oinf μ νE aE (prj (fixF μ (GM.levE L.UE)) ((List.ofFn B).prod (prj (T.typed μ) v)))
      rw [prj_self (hle (hBG.1 _ (prj_mem (typed_closed μ T) v)))])
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      exact (prj_self (hCG.1 _ (prj_mem (typed_closed μ T) v))).symm)
    hθP.eq.symm
  have hCG' : Good ((Uiw μ w₀.1 ν ^ j) ∘L (List.ofFn B).prod) := hCG
  have hfin := hB _ hCG'.2.1 hCG'.2.2
  have htr : trOn (eigIn V 𝔢.toAmp.A (y ^ (m + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) =
      ((κ : ℂ) * ((y ^ (m + 1) : ℝ) : ℂ)) * trOn (eigIn (V ⊓ T.typed μ) (Oinf μ νE aE) (y ^ (m + 1)))
        (((Uiw μ w₀.1 ν ^ j) ∘L (List.ofFn B).prod) ∘L θ.U) := by
    unfold trOn
    rw [← trace_sm, hUq, hKg, hAeq]
    exact congrArg _ hal
  rw [htr, hfin]
  ring
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace =====
