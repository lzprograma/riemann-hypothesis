module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Geometrically.Integral\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc\npublic import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtendDense

open GlobalTheory.GenericExtend GlobalTheory.DvrModel

theorem gm_eq_of_corr {X Y U HU H Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (H ⟶ X)} {ε : I → ℤ} {jH : HU ⟶ H} {e : Y ⟶ H} {j : U ⟶ Y} {eU : U ⟶ HU}
    (heU : eU ≫ jH = j ≫ e)
    {t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (κ : Z ⟶ U) (z : Z) (a : I → L.ι) (ha : e (j (κ z)) ∈ LB.wchart L φ a) :
    gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
      gm (κ ≫ j) z (LB.wchart L (fun i => e ≫ φ i) a) (ρ.s a) := by
  choose Jg hJg using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  have hG : Good L z Jg := hJg
  have hv := val_corr hG hc κ
  rw [val_pull hG, val_pull hG] at hv
  have hw : ∀ k, (κ ≫ eU) ≫ jH ≫ φ k = (κ ≫ j) ≫ e ≫ φ k := fun k => by
    simp only [Category.assoc, reassoc_of% heU]
  let a' : I → L.ι := fun k => Jg ((κ ≫ eU) ≫ jH ≫ φ k)
  have ha' : a' = fun k => Jg ((κ ≫ j) ≫ e ≫ φ k) := funext fun k => congrArg Jg (hw k)
  rw [val_of t (κ ≫ eU) z Jg a' (fun k => rfl),
    val_of ρ (κ ≫ j) z Jg a' (fun k => by rw [ha'])] at hv
  have hpt : jH ((κ ≫ eU) z) = e ((κ ≫ j) z) := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, heU, ← Category.assoc, Scheme.Hom.comp_apply]
  have h1 : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a :=
    (wchart_comp L jH φ a).ge (show jH ((κ ≫ eU) z) ∈ LB.wchart L φ a by rw [hpt]; exact ha)
  have h2 : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a := (wchart_comp L e φ a).ge ha
  have h1' : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a' := hG.mem (fun i => jH ≫ φ i) (κ ≫ eU)
  have h2' : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a' := by
    rw [ha']; exact hG.mem (fun i => e ≫ φ i) (κ ≫ j)
  have htr : trF (L := L) (fun i => jH ≫ φ i) ε (κ ≫ eU) z a a' =
      trF (L := L) (fun i => e ≫ φ i) ε (κ ≫ j) z a a' := by
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [hw k]
  rw [gen_trans ht (κ ≫ eU) z h1 h1', gen_trans hρ (κ ≫ j) z h2 h2', htr, hv]

theorem existsUnique_gen_extend : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  intro Y U H HU X _ j _ _ _ _ hY p e jH pU eU hsm hgi he hP heU L hL I _ φ ε t ρ ht hρ hc
  haveI := hsm
  haveI := hgi
  have := IsNormalScheme.of_pred hY
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have hN : (LB.LinComb L φ ε).IsLB := LB.isLB_linComb hL φ ε
  let iso := hP.isoPullback
  have hiso : iso.inv ≫ jH = pullback.fst p j := hP.isoPullback_inv_fst
  have hiso' : iso.hom ≫ pullback.fst p j = jH := hP.isoPullback_hom_fst
  have hisoa : ∀ {W : Scheme.{0}} (g : H ⟶ W), iso.inv ≫ jH ≫ g = pullback.fst p j ≫ g := fun g => by
    rw [← Category.assoc, hiso]
  have hpt : ∀ q, jH (iso.inv q) = pullback.fst p j q := fun q => by
    rw [← Scheme.Hom.comp_apply, hiso]
  have hle : ∀ a, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤
      iso.inv ⁻¹ᵁ LB.wchart L (fun i => jH ≫ φ i) a := fun a q hq =>
    (wchart_comp L jH φ a).ge (show jH (iso.inv q) ∈ LB.wchart L φ a by rw [hpt]; exact hq)
  let τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ :=
    fun a => res (hle a) (pullU iso.inv _ (t.s a))
  have hτg : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback p j) (z : Z) (a),
      pullback.fst p j (r z) ∈ (LB.LinComb L φ ε).U a →
      gm r z _ (τ a) = gm (r ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) :=
    fun Z r z a h => (gm_res r z (hle a) h _).trans (gm_pull r iso.inv z _ (hle a h) _)
  have hτ : Compat (LB.LinComb L φ ε) (pullback.fst p j) τ := fun Z r z a b ha hb => by
    have ha' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a ha
    have hb' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) b := hle b hb
    rw [hτg Z r z a ha, hτg Z r z b hb, gen_trans ht (r ≫ iso.inv) z ha' hb']
    refine congrArg (· * _) (Eq.symm ((gm_linComb L φ ε (r ≫ pullback.fst p j) z a b ha hb).trans ?_))
    rw [trF]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Category.assoc, hisoa]
  have hle' : ∀ a, e ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤ LB.wchart L (fun i => e ≫ φ i) a :=
    fun a => (wchart_comp L e φ a).ge
  let ρ' : ∀ a, Γ(Y, e ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ := fun a => res (hle' a) (ρ.s a)
  let eU' : U ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 U) (by simp [he])
  have w : eU' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU' ≫ pullback.snd p j = 𝟙 U := pullback.lift_snd _ _ _
  have hsec : eU ≫ pU = 𝟙 U := by
    rw [← cancel_mono j, Category.id_comp, Category.assoc, ← hP.w, reassoc_of% heU, he,
      Category.comp_id]
  have heU' : eU' ≫ iso.inv = eU := by
    rw [← cancel_mono iso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [w, Category.assoc, hiso', heU]
    · rw [hπ, Category.assoc, hP.isoPullback_hom_snd, hsec]
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : I → L.ι),
      e (j (κ z)) ∈ (LB.LinComb L φ ε).U a →
      gm (κ ≫ eU') z (pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ (LB.LinComb L φ ε).U a) (ρ' a) := by
    intro Z κ z a ha
    have hm : pullback.fst p j ((κ ≫ eU') z) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, w]; exact ha
    have e₁ : gm ((κ ≫ eU') ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
        gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      rw [Category.assoc, heU']
    exact (hτg Z _ z a hm).trans (e₁.trans ((gm_eq_of_corr hL heU ht hρ hc κ z a ha).trans
      (gm_res (κ ≫ j) z (hle' a) ha _).symm))
  have key : ∀ a, ∀ y ∈ (LB.LinComb L φ ε).U a, Order.coheight y ≤ 1 →
      y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  let σ : ∀ a, Γ(H, (LB.LinComb L φ ε).U a)ˣ := fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩
  have hσ : ∀ a, pullU (pullback.fst p j) _ (σ a) = τ a := fun a ↦ Units.ext (hs a)
  have hgen : (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)).IsGen := fun a b ↦ Units.map_injective
      (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a ⊓ (LB.LinComb L φ ε).U b)).hom.toMonoidHom)
      (hJ _) (by
    change pullU _ _ _ = pullU _ _ _
    refine unit_ext fun q hq ↦ ?_
    have := hτ _ (𝟙 _) q a b hq.1 hq.2
    rw [← hσ, ← hσ, gm_pull _ _ q _ hq.1, gm_pull _ _ q _ hq.2] at this
    rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, map_mul, gm_res _ q _ hq, gm_res _ q _ hq]
    exact this)
  have hτc : ∀ c : LB.Gen (LB.LinComb L φ ε), LB.pullGen L _ _ c jH = t → ∀ a,
      pullU (pullback.fst p j) _ (c.s a) = τ a := by
    rintro c rfl a
    refine unit_ext fun q hq ↦ ?_
    rw [gm_pull _ _ q _ hq, hτg _ (𝟙 _) q a hq]
    simp only [Category.id_comp]
    dsimp only [LB.pullGen]
    have h₁ : iso.inv q ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a hq
    have h₂ : jH (iso.inv q) ∈ LB.wchart L φ a := by rw [hpt]; exact hq
    exact ((gm_res iso.inv q _ h₁ _).trans ((gm_pull iso.inv jH q _ h₂ _).trans (congrArg (fun f => gm f q _ (c.s a)) hiso))).symm
  have hpg : LB.pullGen L _ _ (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)) jH = t := by
    refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext fun y hy ↦ ?_)
    have hy' : jH y ∈ (LB.LinComb L φ ε).U a := (wchart_comp L jH φ a).le hy
    have h' : pullback.fst p j (iso.hom y) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, hiso']; exact hy'
    have e₁ : gm jH y ((LB.LinComb L φ ε).U a) (σ a) =
        gm (𝟙 HU) y (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      refine (congrArg (fun f => gm f y ((LB.LinComb L φ ε).U a) (σ a)) hiso'.symm).trans
        ((gm_pull iso.hom _ y _ h' _).symm.trans ?_)
      rw [hσ]
      exact (hτg _ iso.hom y a h').trans (by rw [Iso.hom_inv_id])
    refine Eq.trans ?_ e₁
    dsimp only [LB.pullGen]
    rw [gm_res _ y _ hy, gm_pull _ _ y _ hy', Category.id_comp]
  refine ⟨⟨σ⟩, ⟨hgen, hpg⟩, ?_⟩
  rintro ⟨c⟩ ⟨-, hc'⟩
  refine congrArg LB.Gen.mk (funext fun a ↦ Units.map_injective
    (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a)).hom.toMonoidHom) (hJ _) ?_)
  exact (hτc ⟨c⟩ hc' a).trans (hσ a).symm

end GlobalTheory.GenExtendDense
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical\npublic import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB\npublic import Mathlib.AlgebraicGeometry.Geometrically.Integral\npublic import Mathlib.AlgebraicGeometry.Morphisms.Smooth\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen\npublic import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DenseCubeExt

open GlobalTheory.CubTransport GlobalTheory.PolExtension GlobalTheory.CechPic

theorem val_eq_of_inj {X Y Y' : Scheme.{0}} (h : Y' ⟶ Y) (hinj : Function.Injective h.appTop.hom)
    {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hf : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (H : ∀ y J, Good M y J → val u h y J = val u' h y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J :=
  GlobalTheory.NormalCubeExt.val_eq_of_inj h hinj hM hf hu hu' H Z r z J hJ

theorem appTop_injective_fst {S U T : Scheme.{0}} [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (q : T ⟶ S) [Smooth q] :
    Function.Injective (pullback.fst q j).appTop.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have := GlobalTheory.isNormalScheme_of_smooth q
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  exact (pullback.fst q j).app_injective ⊤

section Base

variable {S U : Scheme.{0}} [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) (j : U ⟶ S)
  [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
include hS

theorem corr_of_open {X : Scheme.{0}} (T : Over S) [Smooth T.hom]
    {L : LB X} (hL : L.IsLB) {I I' : Type} [Fintype I] [Fintype I']
    {φ : I → (T.left ⟶ X)} {ε : I → ℤ} {φ' : I' → (T.left ⟶ X)} {ε' : I' → ℤ} (hf : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    (H : ∀ (y : (pullback T.hom j :)) J, Good L y J →
      val t (pullback.fst T.hom j) y J = val t' (pullback.fst T.hom j) y J) :
    LB.Gen.Corr L _ _ _ _ t t' :=
  corr_of_val hL fun y J hJ => val_eq_of_inj (pullback.fst T.hom j) (appTop_injective_fst hS j T.hom) hL hf ht ht'
    H _ _ y J hJ

end Base

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

variable [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) {U : Scheme.{0}} (j : U ⟶ S)
  [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] [Smooth G.hom] [GeometricallyConnected G.hom]
include hS

theorem exists_cubical_of_open (L : RigLB G) (t : LB.Gen (Theta G L.L)) (ht : t.IsGen)
    (h : ∀ (T : Over U) (z : T.left) (J), Good L.L z J →
      IsCub (thV t (T := Over.mk (T.hom ≫ j)) z J)) : ∃ c : CubicalStr G L, c.t = t :=
  GlobalTheory.NormalCubeExt.exists_cubical_of_corr j (fun T _ _ => corr_of_open hS j T) L t ht h

end Group

theorem exists_extension {S : Scheme.{0}} [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    {U H HU X X' : Scheme.{0}} (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (eU : U ⟶ HU) (hs : Smooth p) (hc : GeometricallyConnected p) (he : e ≫ p = 𝟙 _)
    (hp : IsPullback jH pU p j) (heU : eU ≫ jH = j ≫ e) {L : LB X} (hL : L.IsLB) {L' : LB X'} (hL' : L'.IsLB)
    {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) {K : Type} [Fintype K] (φ : K → (H ⟶ X))
    (φ' : K → (HU ⟶ X')) (ε : K → ℤ) (hφ : ∀ k, φ' k ≫ F = jH ≫ φ k)
    (f₁ : FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (S ⟶ X)) PEmpty.elim (fun k => e ≫ φ k) ε)
    (f₂ : FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (U ⟶ X')) PEmpty.elim (fun k => eU ≫ φ' k) ε)
    (s : LB.Gen (LB.LinComb L' φ' ε)) (hg : s.IsGen) (h1 : ∀ y J, Good L' y J → val s eU y J = 1) :
    ∃ c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ PMaps w φ' φ ε s c jH :=
  GlobalTheory.NormalCubeExt.exists_extension_of j e jH eU hL hL' hw φ φ' ε hφ f₁ f₂ s hg h1 fun t ρ ht hρ hcorr =>
    (_root_.GlobalTheory.GenExtendDense.existsUnique_gen_extend S U H HU X j hS p e jH pU eU hs
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hs hc) he hp heU L hL K φ ε t ρ ht hρ hcorr).exists

section Main

variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

variable [IsLocallyNoetherian S] [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
  [Smooth G.hom] [GeometricallyConnected G.hom]

theorem exists_cubical (hS : Geo.Tor.IsNormalScheme S) (gp : IsGrpPullback A G j F) {L : RigLB A} (c : CubicalStr A L)
    (L' : RigLB G) {w : LB.Iso L.L (L'.L.pull F)} (hw : PGen w) :
    ∃ c' : CubicalStr G L', PMaps w (thφ A (x3 A)) (thφ G (x3 G)) thε c.t c'.t (cubeMapOf gp).F3 :=
  have := CubeExtension.smooth_tensor G G
  have := CubeExtension.geometricallyConnected_tensor G G
  GlobalTheory.NormalCubeExt.exists_cubical_of gp c L'
    (fun hc heU h1 => exists_extension hS j (G3 G).hom (eSec (G3 G)) (cubeMapOf gp).F3 (G3 A).hom (eSec (G3 A))
      (CubeExtension.smooth_tensor G (G ⊗ G)) (CubeExtension.geometricallyConnected_tensor G (G ⊗ G))
      (CubeExtension.eSec_comp _) (GlobalTheory.NormalCubeExt.isPullback_tripleProduct_groupPullback gp) heU L'.isLB L.isLB hw
      (thφ G (x3 G)) (thφ A (x3 A)) thε hc (CubeExtension.formEq_origin G) (CubeExtension.formEq_origin A) c.t c.isGen h1)
    (exists_cubical_of_open hS j L')

theorem isSymmetric (hS : Geo.Tor.IsNormalScheme S) (gp : IsGrpPullback A G j F) {L : RigLB A}
    (L' : RigLB G) {w : LB.Iso L.L (L'.L.pull F)} (hw : PGen w) (h : L.IsSymmetric) : L'.IsSymmetric :=
  GlobalTheory.NormalCubeExt.isSymmetric_of gp L' h fun hφ f₁ f₂ s hs h1 =>
    exists_extension hS j G.hom (eSec G) F A.hom (eSec A) inferInstance inferInstance
      (CubeExtension.eSec_comp _) gp.1 (cubeMapOf gp).e_comm L'.isLB L.isLB hw (K := Fin 2)
      ![(ι[G]).left, 𝟙 G.left] ![(ι[A]).left, 𝟙 A.left] ![1, -1] hφ f₁ f₂ s hs h1

end Main

theorem exists_cubical_extension : ∀ (Y U : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (G : Over Y) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (a : A.left ⟶ G.left), IsGrpPullback A G j a → ∀ (L : RigLB A) (c : CubicalStr A L) (M : LB G.left), M.IsLB → LBIso (M.pull a) L.L → ∃ (L' : RigLB G) (c' : CubicalStr G L') (m : CubeMap A G), m.F = a ∧ m.e = j ∧ m.IsPullCubical c c' ∧ (L.IsSymmetric → L'.IsSymmetric) := by
  intro Y U _ j _ _ _ _ hY G _ _ _ _ A _ _ a gp L c M hM H
  obtain ⟨L', h'⟩ := GlobalTheory.NormalCubeExt.exists_rigidified gp L hM H
  obtain ⟨w, hw, hr⟩ := Unif.RigidifyIso.exists_rigidified_iso Y U j G A a (cubeMapOf gp).e_comm L' L h'
  have hw' := (isGen_iff w).1 hw
  obtain ⟨c', hc'⟩ := exists_cubical hY gp c L' hw'
  refine ⟨L', c', cubeMapOf gp, rfl, rfl, ⟨w, hw, hr, ?_⟩, isSymmetric hY gp L' hw'⟩
  exact (maps_iff w _ (thφ G (x3 G)) _ c.t c'.t (cubeMapOf gp).F3 _ ((cubeMapOf gp).theta_le L'.L) (fun _ => rfl)).2 hc'

end GlobalTheory.DenseCubeExt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension =====
