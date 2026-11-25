module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Mathlib.GroupTheory.CosetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCoverStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRing\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.GroupTheory.CosetCover\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section
namespace GlobalTheory.Poinc.FieldConj
open GlobalTheory.Points RatModel
open scoped Pointwise

theorem eq_of_val_eq_fibre {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {X : Scheme.{0}}
    (q : M.Z ⟶ X) [IsAffineHom q] {K : Type} [Field K] (y y' : Sp K ⟶ M.Z) (hyy : y ≫ q = y' ≫ q)
    (h : ∀ b ∈ M.ringOn {z | q z = (y ≫ q) (IsLocalRing.closedPoint K)}, M.val y b = M.val y' b) : y = y' := by
  set x := (y ≫ q) (IsLocalRing.closedPoint K) with hx
  have hxz : q (y (IsLocalRing.closedPoint K)) = x := rfl
  have hxz' : q (y' (IsLocalRing.closedPoint K)) = x := by rw [hx, hyy]; rfl
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsub : ∀ a ∈ M.ringOn (q ⁻¹ᵁ V : Set M.Z), a ∈ M.ringOn {z | q z = x} :=
    fun _ ha => M.ringOn_anti (fun _ hz => show q _ ∈ V from hz ▸ hxV) ha
  have hzU : y (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz]; exact hxV
  have hzU' : y' (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz']; exact hxV
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)
  have hinv : ∀ {w : Sp K ⟶ M.Z} (hw : Set.range w = {w (IsLocalRing.closedPoint K)}) {a : Ω},
      a ∈ M.O (w (IsLocalRing.closedPoint K)) → a ≠ 0 → (a⁻¹ ∈ M.O (w (IsLocalRing.closedPoint K)) ↔ M.val w a ≠ 0) := by
    intro w hw a ha h0
    rw [val_ne_zero_iff hw ⟨a, ha⟩, isUnit_O_iff]; exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  have hpt : y (IsLocalRing.closedPoint K) = y' (IsLocalRing.closedPoint K) :=
    GlobalTheory.Points.point_eq_of_inv_mem_iff o Ω M _ hU _ _ hzU hzU' fun a ha h0 => by
      rw [hinv hr (M.ringOn_le_O hzU ha) h0, hinv hr' (M.ringOn_le_O hzU' ha) h0, h a (hsub a ha)]
  set z := y (IsLocalRing.closedPoint K)
  have hO : ∀ a ∈ M.O z, M.val y a = M.val y' a := fun a ha => by
    obtain ⟨c, hc, d, hd, hd0, hdi, rfl⟩ :=
      GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine o Ω M _ hU z hzU a ha
    have hsp : ∀ w, y w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
    have hsp' : ∀ w, y' w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K), hpt]
    have e1 := val_mul hsp ha (M.ringOn_le_O hzU hd); have e1' := val_mul hsp' ha (M.ringOn_le_O hzU hd)
    rw [div_mul_cancel₀ c hd0] at e1 e1'
    have hne : M.val y d ≠ 0 := (hinv hr (M.ringOn_le_O hzU hd) hd0).1 hdi
    have hne' : M.val y' d ≠ 0 := (h d (hsub d hd)) ▸ hne
    rw [eq_div_of_mul_eq hne e1.symm, eq_div_of_mul_eq hne' e1'.symm, h c (hsub c hc), h d (hsub d hd)]
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local hpt fun W h₁ h₂ => ?_
  ext f
  have e3 := hO _ (valF_mem_O (h₁ (x := IsLocalRing.closedPoint K) trivial) f)
  rw [val_valF ((top_le_preimage_iff y W).1 h₁), val_valF ((top_le_preimage_iff y' W).1 h₂)] at e3
  unfold valF at e3; rw [dite_eq_left h₁, dite_eq_left h₂] at e3
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e3

theorem galConj : ∀ (A F L K : Type) [CommRing A] [IsDomain A] [Field F] [Field L] [Field K] [CharZero K] [Algebra A F] [IsFractionRing A F] [IsIntegrallyClosed A] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [IsGalois F L] (B : Subring L), (∀ b : L, b ∈ B ↔ IsIntegral A b) → ∀ e e' : B →+* K, (∀ b : B, (∃ a : A, algebraMap A L a = b) → e b = e' b) → ∃ σ : L ≃ₐ[F] L, ∀ b c : B, (c : L) = σ b → e' b = e c := by
  intro A F L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ B hB e e' hA
  classical
  let σB : (L ≃ₐ[F] L) → B →+* B := fun σ => ((σ : L →+* L).comp B.subtype).codRestrict B fun b =>
    (hB _).2 (IsIntegral.map ((σ : L →ₐ[F] L).restrictScalars A) ((hB b).1 b.2))
  have claim : ∀ b : B, ∃ σ : L ≃ₐ[F] L, e' b = e (σB σ b) := fun b => by
    let P : Polynomial B := ∏ σ : L ≃ₐ[F] L, (Polynomial.X - Polynomial.C (σB σ b))
    have hPmap : ∀ τ : L ≃ₐ[F] L, (P.map B.subtype).map (τ : L →+* L) = P.map B.subtype := fun τ => by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun _ => rfl
    have hmap : P.map e = P.map e' := by
      ext n; rw [Polynomial.coeff_map, Polynomial.coeff_map]
      obtain ⟨f, hf⟩ := (IsGalois.mem_bot_iff_fixed (P.coeff n : L)).2 fun τ => by
        simpa [Polynomial.coeff_map] using congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) (hPmap τ)
      change algebraMap F L f = _ at hf
      have hint' : IsIntegral A f :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F L) (algebraMap F L).injective).1
          (hf ▸ (hB _).1 (P.coeff n).2)
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
      exact hA _ ⟨a, by rw [IsScalarTower.algebraMap_apply A F L, ha, hf]⟩
    have h0 : (P.map e').eval (e' b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [sub_eq_zero]; exact Subtype.ext rfl), map_zero]
    rw [← hmap] at h0
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨σ, -, hσ⟩ := Finset.prod_eq_zero_iff.1 h0
    exact ⟨σ, sub_eq_zero.1 hσ⟩
  let H : (L ≃ₐ[F] L) → AddSubgroup B := fun σ => (e'.toAddMonoidHom - (e.comp (σB σ)).toAddMonoidHom).ker
  have hmemH : ∀ σ (b : B), b ∈ H σ ↔ e' b = e (σB σ b) := fun _ _ => by simp [H, AddMonoidHom.mem_ker, sub_eq_zero]
  have hcover : ⋃ σ ∈ (Finset.univ : Finset (L ≃ₐ[F] L)), (0 : B) +ᵥ ((H σ : AddSubgroup B) : Set B) = Set.univ :=
    Set.eq_univ_of_forall fun b => let ⟨σ, hσ⟩ := claim b; Set.mem_iUnion₂.2 ⟨σ, Finset.mem_univ _, by
      rw [zero_vadd]; exact (hmemH σ b).2 hσ⟩
  obtain ⟨σ, -, hfin⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcover
  refine ⟨σ, fun b c hc => ?_⟩
  obtain rfl : c = σB σ b := Subtype.ext hc
  have hmem := (hmemH σ _).1 (AddSubgroup.nsmul_index_mem (H σ) b)
  rw [map_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hmem
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hfin.index_ne_zero) hmem

theorem val_algebraMap_of_comp {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
    [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z}
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {K : Type} [Field K] (y : Sp K ⟶ M₂.Z) {x : Ω₁}
    (hx : x ∈ M₁.O ((y ≫ q) (IsLocalRing.closedPoint K))) :
    M₂.val y (algebraMap Ω₁ Ω₂ x) = M₁.val (y ≫ q) x := by
  obtain ⟨U, f, hzU, rfl⟩ := hx
  have h1 : Set.range (y ≫ q) ⊆ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  have h2 : Set.range y ⊆ q ⁻¹ᵁ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  rw [← GlobalTheory.Poinc.FinPts.valF_app hg ⟨_, hzU⟩ f, val_valF h2, val_valF h1]
  exact (valR_comp y q U f).symm

theorem exists_aut_eq_of_comp_eq : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ _ _ M₁ M₂ q hN₁ hN₂ hF hg K _ _ y y' hyy
  set z₁ := (y ≫ q) (IsLocalRing.closedPoint K) with hz₁
  have : IsIntegrallyClosed (M₁.O z₁) := isIntegrallyClosed_O hN₁ z₁
  let B : Subring Ω₂ := (M₂.ringOn {z | q z = z₁}).toSubring
  have hB : ∀ b : Ω₂, b ∈ B ↔ IsIntegral (M₁.O z₁) b := fun b => by
    let : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
    have h1 := (GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg z₁).1 b
    have h2 : IsIntegral (M₁.Z.presheaf.stalk z₁) b ↔ IsIntegral (M₁.O z₁) b :=
      ⟨fun hb => IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).toRingHom (RingHom.id Ω₂) (RingHom.ext fun _ => rfl) hb,
       fun hb => IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).symm.toRingHom (RingHom.id Ω₂) (RingHom.ext fun x => by
         show algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ ((M₁.stalkEquiv z₁).symm x)) = algebraMap Ω₁ Ω₂ (x : Ω₁)
         rw [← coe_stalkEquiv, RingEquiv.apply_symm_apply]) hb⟩
    rw [← h2, ← mem_integralClosure_iff, h1, Subalgebra.mem_toSubring, mem_ringOn]; rfl
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)
  let e : B →+* K := (M₂.valHom y _ hr).comp
    (Subring.inclusion (show B ≤ (M₂.O (y (IsLocalRing.closedPoint K))).toSubring from
      fun _ hb => mem_ringOn.1 hb _ rfl))
  let e' : B →+* K := (M₂.valHom y' _ hr').comp
    (Subring.inclusion (show B ≤ (M₂.O (y' (IsLocalRing.closedPoint K))).toSubring from
      fun _ hb => mem_ringOn.1 hb _ (by rw [hz₁, hyy]; rfl)))
  have hA : ∀ b : B, (∃ a : M₁.O z₁, algebraMap (M₁.O z₁) Ω₂ a = b) → e b = e' b := by
    rintro b ⟨a, hab⟩
    change M₂.val y b = M₂.val y' b
    rw [← hab]
    show M₂.val y (algebraMap Ω₁ Ω₂ a) = M₂.val y' (algebraMap Ω₁ Ω₂ a)
    rw [val_algebraMap_of_comp hg y a.2, val_algebraMap_of_comp hg y' (by rw [← hyy]; exact a.2), hyy]
  obtain ⟨σ, hσ⟩ := galConj (M₁.O z₁) Ω₁ Ω₂ K B hB e e' hA
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.Poinc.GalAut.autAct o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg σ
  have := hF
  have key : y ≫ s = y' := eq_of_val_eq_fibre M₂ q (y ≫ s) y' (by rw [Category.assoc, hs2, hyy]) fun b hb => by
    rw [show (y ≫ s) ≫ q = y ≫ q from by rw [Category.assoc, hs2]] at hb
    rw [hs3]
    exact (hσ ⟨b, hb⟩ ⟨σ b, (hB _).2 (IsIntegral.map ((σ : Ω₂ →ₐ[Ω₁] Ω₂).restrictScalars (M₁.O z₁)) ((hB b).1 hb))⟩ rfl).symm
  exact ⟨σ, s, hs1, key, fun b => key ▸ hs3 K y b⟩

end GlobalTheory.Poinc.FieldConj
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCoverStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCoverStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCoverStatement =====
