module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier
open scoped CategoryTheory.Obj
open GlobalTheory.Desc TensorProduct

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegular, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbeds, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChange, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjoint

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegular =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegular", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
namespace GlobalTheory.Desc.BCChart

def ev {T : Scheme.{0}} {K : Type} [CommRing K] (f : Sp K ⟶ T) (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (u : Γ(T, O)) : K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((f.appLE O ⊤ h).hom u)

theorem ev_comp {T T' : Scheme.{0}} {K : Type} [CommRing K] (s : Sp K ⟶ T') (g : T' ⟶ T) {O : T.Opens}
    {O' : T'.Opens} (e : O' ≤ g ⁻¹ᵁ O) (h : ⊤ ≤ s ⁻¹ᵁ O') {g' : Sp K ⟶ T} (hg : s ≫ g = g')
    (h' : ⊤ ≤ g' ⁻¹ᵁ O) (u : Γ(T, O)) : ev g' O h' u = ev s O' h ((g.appLE O O' e).hom u) := by
  subst hg; unfold ev; congr 1; rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_top_top {A B : Scheme.{0}} (f : A ⟶ B) : f.appLE ⊤ ⊤ le_top = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl

theorem ev_spMap {T : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (θ : A →+* B) (f : Sp A ⟶ T)
    (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ (spMap θ ≫ f) ⁻¹ᵁ O) (u : Γ(T, O)) :
    ev (spMap θ ≫ f) O h' u = θ (ev f O h u) := by
  rw [ev_comp (spMap θ) f h le_top rfl]
  unfold ev; rw [appLE_top_top, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]; rfl

theorem fromSpecStalk_top' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun z _ =>
  ((Scheme.range_fromSpecStalk (X := X)).subset ⟨z, rfl⟩).mem_open U.2 hx

theorem fromSpecStalk_appLE' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top' x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top' x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem fnOf_eq_ev {X : Scheme.{0}} [IsIntegral X] (O : X.Opens) (hO : genericPoint X ∈ O) (u : Γ(X, O)) :
    fnOf O hO u = ev (gp X) O (fromSpecStalk_top' _ O hO) u := by
  unfold ev gp; rw [fromSpecStalk_appLE' _ O hO, CommRingCat.comp_apply]
  change _ = (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom _
  rw [Iso.inv_hom_id_apply]; rfl

theorem exists_tensor_fnOf : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (U : X.Opens), IsAffineOpen U → ∀ hg : genericPoint X ∈ U, letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra; letI := ρ.toAlgebra; ∃ β : Γ(X, U) ⊗[R] R₁ →+ Y.functionField, Function.Injective β ∧ (∀ b r, β (b ⊗ₜ[R] r) = θ (GlobalTheory.Cartier.fnOf U hg b) * GlobalTheory.Desc.cst q r) ∧ Set.range β = {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  intro R R₁ _ _ ρ X Y V _ _ p q i _ φ θ H hP U hU hg
  let := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  let := ρ.toAlgebra
  obtain ⟨l, hl1, hl2⟩ := hP
  let W : V.Opens := φ ⁻¹ᵁ U ⊓ (i ≫ q) ⁻¹ᵁ ⊤
  let O : Y.Opens := i ''ᵁ W
  have hmemO : ∀ y : Y, y ∈ O ↔ ∃ z : V, φ z ∈ U ∧ i z = y :=
    fun _ => ⟨fun ⟨z, hz, e⟩ => ⟨z, hz.1, e⟩, fun ⟨z, hz, e⟩ => ⟨z, ⟨hz, trivial⟩, e⟩⟩
  let pt : Sp Y.functionField := IsLocalRing.closedPoint Y.functionField
  have hz1 : i (l pt) = genericPoint Y := by rw [← Scheme.Hom.comp_apply, hl1]; exact Scheme.fromSpecStalk_closedPoint
  have hz2 : φ (l pt) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, hl2, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecStalk_closedPoint (x := genericPoint X) ▸ congrArg _ (Subsingleton.elim _ _)
  have hO : genericPoint Y ∈ O := (hmemO _).2 ⟨l pt, hz2 ▸ hg, hz1⟩
  let e := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p (i ≫ q) φ H U hU
  let j : Γ(V, W) →+* Γ(Y, O) := (i.appIso W).inv.hom
  have hj : ∀ s, j ((i.appIso W).hom.hom s) = s := fun _ => Iso.hom_inv_id_apply _ _
  have hj' : ∀ s, (i.appIso W).hom.hom (j s) = s := fun _ => Iso.inv_hom_id_apply _ _
  refine ⟨((fnOf O hO).comp (j.comp e.toRingHom)).toAddMonoidHom, fun a b hab => e.injective ?_, fun b r => ?_, ?_⟩
  · have h1 := congrArg (i.appIso W).hom.hom (fnOf_injective O hO hab)
    simp only [RingHom.comp_apply, hj'] at h1
    exact h1
  · have hlW : ⊤ ≤ l ⁻¹ᵁ W := fun z _ => by
      have hz := Subsingleton.elim z pt; subst hz; exact ⟨show φ (l pt) ∈ U by rw [hz2]; exact hg, trivial⟩
    have hC : ∀ y : Γ(V, W), fnOf O hO (j y) = ev l W hlW y := fun y => by
      rw [fnOf_eq_ev]
      refine (ev_comp l i (O := O) (O' := W) (i.preimage_image_eq W).ge hlW hl1 _ _).trans ?_
      congr 1; rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
      have : (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) := rfl
      erw [this, CategoryTheory.Functor.map_id]; rfl
    have hX : ⊤ ≤ (spMap θ ≫ gp X) ⁻¹ᵁ U := fun z _ => fromSpecStalk_top' (genericPoint X) U hg (Set.mem_univ (spMap θ z))
    have hYq : ⊤ ≤ (gp Y ≫ q) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    show fnOf O hO (j (e (b ⊗ₜ[R] r))) = _
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul, map_mul, map_mul, hC, hC]
    congr 1
    · rw [← ev_comp l φ inf_le_left hlW hl2 hX, ev_spMap θ (gp X) U (fromSpecStalk_top' _ U hg), ← fnOf_eq_ev]
    · simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, cst, RingHom.comp_apply]
      rw [fnOf_eq_ev ⊤ trivial, ← appLE_top_top, ← ev_comp l (i ≫ q) le_top hlW (by rw [← Category.assoc, hl1]) hYq,
        ← ev_comp (gp Y) q le_top (fromSpecStalk_top' _ ⊤ trivial) rfl hYq]
  · ext v; simp only [Set.mem_range, Set.mem_ofPred_eq]
    refine ⟨fun ⟨t, ht⟩ z hz => ht ▸ regAt_fnOf ((hmemO _).2 ⟨z, hz, rfl⟩) hO _, fun hv => ?_⟩
    obtain ⟨s, hs⟩ := exists_fnOf_eq hO fun y hy => let ⟨z, hz, e⟩ := (hmemO y).1 hy; e ▸ hv z hz
    exact ⟨e.symm ((i.appIso W).hom.hom s), by show fnOf O hO (j (e (e.symm _))) = v; rw [RingEquiv.apply_symm_apply, hj, hs]⟩

end GlobalTheory.Desc.BCChart
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegular =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbeds =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbeds", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
namespace GlobalTheory.Desc.FlatLinDisj

theorem linDisj_of_flat (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁]
    [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L)
    (h : ∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) :
    LinDisj (algebraMap R K) c θ := by
  intro n u hu r hr
  let f : (Fin n → R) →ₗ[R] K := Fintype.linearCombination R u
  have hf : Function.Injective f := LinearMap.ker_eq_bot.1 <| LinearMap.ker_eq_bot'.2 fun a ha =>
    hu a (by simpa [f, Fintype.linearCombination_apply, Algebra.smul_def] using ha)
  set x : (Fin n → R) ⊗[R] R₁ := ∑ j, Pi.single j 1 ⊗ₜ[R] r j
  have hx0 : x = 0 := Module.Flat.rTensor_preserves_injective_linearMap f hf <| by
    simpa [x, map_sum, LinearMap.rTensor_tmul, f, Fintype.linearCombination_apply_single] using h n u r hr
  funext i
  simpa [x, map_sum, LinearMap.rTensor_tmul, Pi.single_apply] using
    congrArg (fun z => TensorProduct.lid R R₁ ((LinearMap.proj (R := R) (φ := fun _ : Fin n => R) i).rTensor R₁ z)) hx0

end GlobalTheory.Desc.FlatLinDisj
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbeds =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbeds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChange =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChange", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
namespace GlobalTheory.Desc.FlatInter

theorem exists_fin_sum {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M ⊗[R] N) : ∃ (n : ℕ) (u : Fin n → M) (r : Fin n → N), x = ∑ i, u i ⊗ₜ[R] r i := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact ⟨1, fun _ => m, fun _ => n, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, u, r, rfl⟩ := hx; obtain ⟨m, u', r', rfl⟩ := hy
    exact ⟨n + m, Fin.append u u', Fin.append r r', by simp [Fin.sum_univ_add]⟩

theorem mem_range_iInf {R K R₁ : Type} [CommRing R] [AddCommGroup K] [Module R K] [AddCommGroup R₁] [Module R R₁]
    [Module.Flat R R₁] {J : Type} [Finite J] (N : J → Submodule R K) (T : K ⊗[R] R₁)
    (hT : ∀ j, T ∈ LinearMap.range ((N j).subtype.rTensor R₁)) :
    T ∈ LinearMap.range ((⨅ j, N j).subtype.rTensor R₁) := by
  classical
  have := Fintype.ofFinite J
  let π : K →ₗ[R] ∀ j, K ⧸ N j := LinearMap.pi fun j => (N j).mkQ
  have hex : Function.Exact (⨅ j, N j).subtype π := by rw [LinearMap.exact_iff]; simp [π, LinearMap.ker_pi]
  rw [← LinearMap.exact_iff.mp (Module.Flat.rTensor_exact R₁ hex), LinearMap.mem_ker]
  let e := TensorProduct.piLeft R R₁ (fun j => K ⧸ N j)
  apply e.injective; rw [map_zero]; funext j
  have hj : LinearMap.proj j ∘ₗ e.toLinearMap ∘ₗ π.rTensor R₁ = (N j).mkQ.rTensor R₁ := by ext x r; simp [π, e]
  have := congrArg (· T) hj
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_proj, Function.eval] at this
  rw [this, Pi.zero_apply, ← LinearMap.mem_ker, rTensor_mkQ]
  exact hT j

def tensorMap {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K]
    (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) :
    K ⊗[R] R₁ →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun r => c r * θ u) (fun _ _ => by simp [add_mul]))
      (fun _ _ => by ext; simp [mul_add]))
    (fun a u r => by simp only [AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, hc]; ring)

theorem tensorMap_tmul {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁]
    [Algebra R K] (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a))
    (u : K) (r : R₁) : tensorMap θ c hc (u ⊗ₜ[R] r) = c r * θ u := rfl

end GlobalTheory.Desc.FlatInter

open GlobalTheory.Desc.FlatInter in
theorem GlobalTheory.Desc.spanBy_iInter_of_flat : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) → (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → ∀ (J : Type) [Finite J] [Nonempty J] (N : J → Submodule R K), spanBy c (θ '' ⋂ j, (N j : Set K)) = ⋂ j, spanBy c (θ '' (N j : Set K)) := by
  intro R R₁ K L _ _ _ _ _ _ _ θ c hc hinj J _ _ N
  let Φ := tensorMap θ c hc
  have hΦ : ∀ x, Φ x = 0 → x = 0 := fun x hx =>
    let ⟨n, u, r, e⟩ := exists_fin_sum x; e ▸ hinj n u r (by simpa [Φ, e, map_sum, tensorMap_tmul] using hx)
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact Set.mem_iInter.2 fun j => ⟨n, r, t, fun i => Set.image_mono (Set.iInter_subset _ j) (ht i), rfl⟩
  · intro hv
    have key : ∀ j, ∃ T ∈ LinearMap.range ((N j).subtype.rTensor R₁), Φ T = v := fun j => by
      obtain ⟨n, r, t, ht, rfl⟩ := Set.mem_iInter.1 hv j
      choose u hu hut using ht
      exact ⟨(N j).subtype.rTensor R₁ (∑ i, (⟨u i, hu i⟩ : N j) ⊗ₜ[R] r i), LinearMap.mem_range_self _ _,
        by simp [Φ, map_sum, tensorMap_tmul, hut]⟩
    choose T hT hTv using key
    obtain ⟨j₀⟩ := ‹Nonempty J›
    obtain ⟨y, hy⟩ := mem_range_iInf N (T j₀) fun j =>
      sub_eq_zero.1 (hΦ (T j - T j₀) (by rw [map_sub, hTv, hTv, sub_self])) ▸ hT j
    obtain ⟨n, w, s, rfl⟩ := exists_fin_sum y
    exact ⟨n, s, fun i => θ (w i), fun i => ⟨w i, Set.mem_iInter.2 fun j => (Submodule.mem_iInf N).1 (w i).2 j, rfl⟩,
      by rw [← hTv j₀, ← hy]; simp [Φ, map_sum, tensorMap_tmul]⟩
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChange =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective", "h": "module\n\npublic import Mathlib.LinearAlgebra.TensorProduct.Defs\npublic import Mathlib.RingTheory.Localization.FractionRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy\npublic import Mathlib.Algebra.BigOperators.GroupWithZero.Action\npublic import Mathlib.Algebra.BigOperators.Ring.Finset\nimport Mathlib.CategoryTheory.Monoidal.Cartesian.Basic\nimport Mathlib.CategoryTheory.Monoidal.Category\nimport Mathlib.CategoryTheory.Monoidal.Mon\npublic import Mathlib.LinearAlgebra.TensorProduct.Map\npublic import Mathlib.RingTheory.Localization.Integer\nimport Mathlib.Topology.Sheaves.Presheaf\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
theorem GlobalTheory.tensor_fraction_injective_of_injective
    (R R₁ B K L : Type) [CommRing R] [CommRing R₁] [CommRing B] [Field K] [Field L] [Algebra R R₁]
    [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsFractionRing B K]
    (θ : K →+* L) (c : R₁ →+* L) (β : B ⊗[R] R₁ →+ L) (hβ : Function.Injective β)
    (hβt : ∀ b r, β (b ⊗ₜ[R] r) = θ (algebraMap B K b) * c r)
    (n : ℕ) (u : Fin n → K) (r : Fin n → R₁) (h : ∑ j, c (r j) * θ (u j) = 0) :
    ∑ j, u j ⊗ₜ[R] r j = 0 := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) (Finset.univ : Finset (Fin n)) u
  choose x hx using fun j => hs j (Finset.mem_univ j)
  have hx' : ∀ j, algebraMap B K (x j) = algebraMap B K (s : B) * u j := fun j => by rw [hx j, Algebra.smul_def]
  have h0 : ∑ j, x j ⊗ₜ[R] r j = 0 := hβ <| by
    rw [map_sum, map_zero]; simp only [hβt, hx', map_mul]
    calc ∑ j, θ (algebraMap B K (s : B)) * θ (u j) * c (r j)
        = θ (algebraMap B K (s : B)) * ∑ j, c (r j) * θ (u j) := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h, mul_zero]
  have h1 := congrArg ((IsScalarTower.toAlgHom R B K).toLinearMap.rTensor R₁) h0
  simp only [map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', map_zero] at h1
  have h2 : (algebraMap B K (s : B)) • ∑ j, u j ⊗ₜ[R] r j = 0 := by
    rw [Finset.smul_sum]; simpa only [TensorProduct.smul_tmul', smul_eq_mul, hx'] using h1
  have := congrArg ((algebraMap B K (s : B))⁻¹ • ·) h2
  rwa [smul_zero, inv_smul_smul₀ (IsLocalization.map_units K s).ne_zero] at this
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement", "h": "module\n\npublic import Mathlib.LinearAlgebra.TensorProduct.Defs\npublic import Mathlib.RingTheory.Localization.FractionRing\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy\nimport Mathlib.CategoryTheory.Monoidal.Cartesian.Basic\nimport Mathlib.CategoryTheory.Monoidal.Category\nimport Mathlib.CategoryTheory.Monoidal.Mon\nimport Mathlib.Topology.Sheaves.Presheaf\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjoint =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjoint", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegular\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChange\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.QuasiAffine\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
namespace GlobalTheory.SecFlatBC

section Helpers

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁]

theorem zero_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) {a b : F₁} (ha : a ∈ spanBy c T) (hb : b ∈ spanBy c T) :
    a + b ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := ha; obtain ⟨m, r', t', ht', rfl⟩ := hb
  exact ⟨n + m, Fin.append r r', Fin.append t t',
    Fin.addCases (fun i => by simpa using ht i) (fun i => by simpa using ht' i), by simp [Fin.sum_univ_add]⟩

theorem spanBy_mul (c : R₁ →+* F₁) (T : Set F₁) (w : F₁) :
    spanBy c ((w * ·) '' T) = (w * ·) '' spanBy c T := by
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose s hs e using ht
    exact ⟨∑ i, c (r i) * s i, ⟨n, r, s, hs, rfl⟩,
      by dsimp only; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [← e i]; ring⟩
  · rintro ⟨_, ⟨n, r, t, ht, rfl⟩, rfl⟩
    exact ⟨n, r, fun i => w * t i, fun i => ⟨_, ht i, rfl⟩,
      by dsimp only; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring⟩

end Helpers

theorem fnOf_algX {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (U : X.Opens)
    (hg : genericPoint X ∈ U) (a : R) :
    GlobalTheory.Cartier.fnOf U hg (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = GlobalTheory.Desc.cst p a :=
  X.presheaf.germ_res_apply (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ from le_top)) (genericPoint X) hg _

theorem span_chart {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {X Y V : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Sp R} {q : Y ⟶ Sp R₁} {i : V ⟶ Y} [IsOpenImmersion i] {φ : V ⟶ X}
    {θ : X.functionField →+* Y.functionField} (H : IsPullback φ (i ≫ q) p (spMap ρ)) (hP : PFF i φ θ)
    {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) :
    spanBy (GlobalTheory.Desc.cst q) (θ '' Set.range (GlobalTheory.Cartier.fnOf U hg)) =
      {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  let := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  let := ρ.toAlgebra
  obtain ⟨β, -, hβ, hr⟩ := _root_.GlobalTheory.Desc.BCChart.exists_tensor_fnOf R R₁ ρ X Y V p q i φ θ H hP U hU hg
  rw [← hr]; ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose a ha e using ht; choose b hb using ha
    exact ⟨∑ j, b j ⊗ₜ[R] r j, by rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hβ, hb, e, _root_.mul_comm]⟩
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul b r => exact ⟨1, fun _ => r, fun _ => θ (GlobalTheory.Cartier.fnOf U hg b), fun _ => ⟨_, ⟨b, rfl⟩, rfl⟩, by simp [hβ, _root_.mul_comm]⟩
    | add x y hx hy => rw [map_add]; exact add_mem_spanBy _ _ hx hy

private theorem inv_mul_regAt_eq {V Y : Scheme.{0}} [IsIntegral Y] (f : V → Y) (D : CartierDiv Y) {P : V → Prop}
    (g : Y.functionFieldˣ) (hg : ∀ z, P z → D.IsEqn (f z) g) :
    ((g : Y.functionField)⁻¹ * ·) '' {w | ∀ z, P z → GlobalTheory.Cartier.RegAt (f z) w} =
      {v | ∀ z, P z → D.RegularAt (f z) v} := by
  ext v; constructor
  · rintro ⟨w, hw, rfl⟩ z hz
    rw [(hg z hz).regularAt_iff, _root_.mul_comm _ (g : Y.functionField), ← _root_.mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero _), _root_.one_mul]
    exact hw z hz
  · intro hv
    refine ⟨v * g, fun z hz => (hg z hz).regularAt_iff.1 (hv z hz), ?_⟩
    dsimp only; rw [_root_.mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), _root_.one_mul]

theorem sections_linDisj_flatBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  intro R R₁ _ _ ρ hρ X Y V _ _ p q i _ φ θ _ _ H hP D D₁ hD
  let : Algebra R X.functionField := (GlobalTheory.Desc.cst p).toAlgebra
  let : Algebra R R₁ := ρ.toAlgebra
  have : Module.Flat R R₁ := hρ
  obtain ⟨U₀, hU₀, hg₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  have hc : ∀ a : R, θ (algebraMap R X.functionField a) = GlobalTheory.Desc.cst q (algebraMap R R₁ a) := fun a => by
    let := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    obtain ⟨β, -, hβ, -⟩ := _root_.GlobalTheory.Desc.BCChart.exists_tensor_fnOf R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    have e := congrArg β (show (algebraMap R Γ(X, U₀) a) ⊗ₜ[R] (1 : R₁) = 1 ⊗ₜ[R] (algebraMap R R₁ a) by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul])
    simp only [hβ, _root_.map_one, _root_.mul_one, _root_.one_mul] at e
    rw [← e]
    exact congrArg θ (fnOf_algX p U₀ hg₀ a).symm
  have hinj : ∀ (n : ℕ) (u : Fin n → X.functionField) (r : Fin n → R₁),
      ∑ j, GlobalTheory.Desc.cst q (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
    let := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    have : Nonempty U₀ := ⟨⟨_, hg₀⟩⟩
    have : IsFractionRing Γ(X, U₀) X.functionField := functionField_isFractionRing_of_isAffineOpen X U₀ hU₀
    have : IsScalarTower R Γ(X, U₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => (fnOf_algX p U₀ hg₀ a).symm
    obtain ⟨β, hβi, hβ, -⟩ := _root_.GlobalTheory.Desc.BCChart.exists_tensor_fnOf R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    exact _root_.GlobalTheory.tensor_fraction_injective_of_injective R R₁ Γ(X, U₀) X.functionField Y.functionField θ
      (GlobalTheory.Desc.cst q) β hβi hβ
  refine ⟨_root_.GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hinj, fun k => ?_⟩
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g : X.functionFieldˣ), IsAffineOpen U ∧ x ∈ U ∧ ∀ y ∈ U, D.IsEqn y g := fun x =>
    let ⟨W, hxW, g, hg⟩ := D.exists_isEqn_nhds x
    let ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hxW
    ⟨U, g, hU, hxU, fun y hy => hg y (hUW hy)⟩
  choose U g hUa hxU hUg using hloc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have cov : ∀ y : X, ∃ j : t, y ∈ U j.1 := fun y => let ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y)); ⟨⟨a, ha⟩, h⟩
  have : Nonempty t := ⟨(cov (genericPoint X)).choose⟩
  have hgen : ∀ j : t, genericPoint X ∈ U j.1 := fun j => GlobalTheory.Cartier.gen_mem (hxU j.1)
  let N : t → Submodule R X.functionField := fun j =>
    { carrier := {u | ∀ y ∈ U j.1, (k • D).RegularAt y u}
      add_mem' := fun ha hb y hy => (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => ((k • D).vanishesAt_zero y).regularAt
      smul_mem' := fun a u hu y hy => Algebra.smul_def a u ▸ (hu y hy).regAt_mul (GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial _) }
  have hSec : Sec D k = ⋂ j, (N j : Set X.functionField) :=
    Set.ext fun u => by rw [Set.mem_iInter]; exact ⟨fun h j y _ => h y, fun h y => let ⟨j, hj⟩ := cov y; h j y hj⟩
  have hrange : ∀ j : t, Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j)) = {w | ∀ y ∈ U j.1, GlobalTheory.Cartier.RegAt y w} :=
    fun j => Set.ext fun _ => ⟨fun ⟨b, hb⟩ y hy => hb ▸ GlobalTheory.Cartier.regAt_fnOf hy (hgen j) b, GlobalTheory.Cartier.exists_fnOf_eq (hgen j)⟩
  have hN : ∀ j : t, (N j : Set X.functionField) =
      ((((g j.1 ^ k : X.functionFieldˣ) : X.functionField)⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := fun j => by
    rw [hrange j]; exact (inv_mul_regAt_eq id (k • D) (g j.1 ^ k) fun y hy => (hUg j.1 y hy).nsmul k).symm
  have hspan : ∀ j : t, spanBy (GlobalTheory.Desc.cst q) (θ '' (N j : Set X.functionField)) =
      {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := fun j => by
    have himg : θ '' ((((g j.1 ^ k : X.functionFieldˣ) : X.functionField)⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) =
        (θ ((g j.1 ^ k : X.functionFieldˣ) : X.functionField)⁻¹ * ·) '' (θ '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
      simp only [Set.image_image, map_mul]
    rw [hN j, himg, spanBy_mul, span_chart H hP (hUa j.1) (hgen j), map_inv₀]
    exact inv_mul_regAt_eq i (k • D₁) (Units.map θ.toMonoidHom (g j.1 ^ k)) fun z hz => by
      rw [map_pow]; exact (hD z _ (hUg j.1 _ hz)).nsmul k
  have hT : {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = ⋂ j : t, {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} :=
    Set.ext fun v => by rw [Set.mem_iInter]; exact ⟨fun h j z _ => h z, fun h z => let ⟨j, hj⟩ := cov (φ z); h j z hj⟩
  rw [hT, hSec, _root_.GlobalTheory.Desc.spanBy_iInter_of_flat R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hc hinj t N]
  exact Set.iInter_congr fun j => (hspan j).symm

end GlobalTheory.SecFlatBC
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjoint =====
