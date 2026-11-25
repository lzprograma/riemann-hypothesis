module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MajorantSquareBound, Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MajorantSquareBound =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MajorantSquareBound", "h": "module\n\npublic import Mathlib.NumberTheory.Padics.Complex\npublic import Mathlib.NumberTheory.Padics.PadicIntegers\npublic import Mathlib.RingTheory.Henselian\npublic import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem\npublic import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs\npublic import Mathlib.RingTheory.Polynomial.Vieta\n\n"}
section -- clump:auto
@[expose] public section

open Finset MvPolynomial in
private theorem exF {B S : Type} [CommRing B] [CommRing S] [Algebra B S] {m : ℕ} (Q : Polynomial B)
    (θ : Fin m → S) (hQ : Q.map (algebraMap B S) = ∏ i, (Polynomial.X - Polynomial.C (θ i))) (r : ℕ) :
    ∃ F : Polynomial B, F.map (algebraMap B S) = ∏ I ∈ powersetCard r univ, (Polynomial.X - Polynomial.C (∏ i ∈ I, θ i)) := by
  let P : Polynomial (MvPolynomial (Fin m) B) := ∏ I ∈ powersetCard r univ, (Polynomial.X - Polynomial.C (∏ i ∈ I, X i))
  have hsym (j : ℕ) : (P.coeff j).IsSymmetric := fun e => by
    simpa [Polynomial.coeff_map] using congrArg (fun p => p.coeff j) <| show P.map (rename e).toRingHom = P by
      simp_rw [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      conv_rhs => rw [← map_univ_equiv e, powersetCard_map]
      simp [-map_univ_equiv, map_prod]
  rw [show (∏ I ∈ powersetCard r univ, (Polynomial.X - Polynomial.C (∏ i ∈ I, θ i))) = P.map (aeval θ).toRingHom by simp [P, Polynomial.map_prod, map_prod]]
  change _ ∈ Polynomial.lifts (algebraMap B S); rw [Polynomial.lifts_iff_coeff_lifts]; intro j
  obtain ⟨E, hE⟩ := esymmAlgHom_fin_surjective B le_rfl ⟨P.coeff j, hsym j⟩
  let b (k : Fin m) : B := (-1) ^ ((k : ℕ) + 1) * Q.coeff (m - ((k : ℕ) + 1))
  refine ⟨aeval b E, ?_⟩
  suffices hhom : (Algebra.ofId B S).comp (aeval b) = (aeval θ).comp (aeval fun k : Fin m => esymm (Fin m) B (k + 1)) by
    simpa [Polynomial.coeff_map, ← esymmAlgHom_apply, congrArg Subtype.val hE] using DFunLike.congr_fun hhom E
  refine algHom_ext fun k => ?_
  have h1 : (Q.map (algebraMap B S)).coeff (m - ((k : ℕ) + 1)) = (-1) ^ ((k : ℕ) + 1) * (univ.val.map θ).esymm ((k : ℕ) + 1) := by
    rw [show Q.map (algebraMap B S) = ((univ.val.map θ).map (Polynomial.X - Polynomial.C ·)).prod by rw [hQ, Multiset.map_map]; rfl, Multiset.prod_X_sub_C_coeff _ (by simp)]
    simp [Nat.sub_sub_self k.2]
  simp only [b, AlgHom.comp_apply, Algebra.ofId_apply, aeval_X, aeval_esymm_eq_multiset_esymm, map_mul, map_pow, map_neg, map_one]
  rw [← Polynomial.coeff_map, h1, ← mul_assoc, ← mul_pow]; simp

open Polynomial Finset in
private theorem isLocalRing_integralClosure {B : Type} [CommRing B] [IsDomain B] [HenselianLocalRing B] :
    IsLocalRing (integralClosure B (AlgebraicClosure (FractionRing B))) := by
  classical
  let Ω := AlgebraicClosure (FractionRing B); let S := integralClosure B Ω
  have hinj : Function.Injective (algebraMap B S) := fun a b h =>
    IsFractionRing.injective B (FractionRing B) ((algebraMap (FractionRing B) Ω).injective (congrArg Subtype.val h))
  obtain ⟨n2, hn2⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨n2, hn2, fun n1 hn1 => hn1.eq_of_le hn2.ne_top fun θ0 h1 => ?_⟩
  by_contra h2; obtain ⟨Q, hQm, hQ0⟩ := Algebra.IsIntegral.isIntegral (R := B) θ0
  let s : Multiset Ω := (Q.map (algebraMap B Ω)).roots; let L := s.toList
  let θ (i : Fin L.length) : S := ⟨L[i], Q, hQm, by simpa [eval_map] using (mem_roots'.mp (Multiset.mem_toList.mp (L.getElem_mem i.2))).2⟩
  have hQ : Q.map (algebraMap B S) = ∏ i, (X - C (θ i)) := by
    apply map_injective (algebraMap S Ω) Subtype.val_injective
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, (IsAlgClosed.splits _).eq_prod_roots_of_monic (hQm.map _),
      show (Q.map (algebraMap B Ω)).roots = (L : Multiset Ω) from (Multiset.coe_toList s).symm, Multiset.map_coe, Multiset.prod_coe, Fin.prod_univ_def, Polynomial.map_list_prod]
    exact congrArg List.prod (List.ext_getElem (by simp) fun i _ _ => by simp [θ])
  obtain ⟨i0, -, hi0'⟩ := prod_eq_zero_iff.mp (by rw [← eval_prod (x := θ0), ← hQ, eval_map]; exact hQ0)
  obtain rfl : θ0 = θ i0 := by simpa [sub_eq_zero] using hi0'
  have hker (n : Ideal S) (hn : n.IsMaximal) (b : B) : algebraMap B S b ∈ n ↔ b ∈ IsLocalRing.maximalIdeal B := by
    rw [← Ideal.mem_under, IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) n)]
  let a := (Q.map (IsLocalRing.residue B)).rootMultiplicity 0; let r := L.length - a
  have hmapn (n : Ideal S) : Q.map ((Ideal.Quotient.mk n).comp (algebraMap B S)) = ∏ i, (X - C (Ideal.Quotient.mk n (θ i))) := by rw [← Polynomial.map_map, hQ, Polynomial.map_prod]; simp
  have hcard (n : Ideal S) (hn : n.IsMaximal) : (univ.filter (θ · ∈ n)).card = a := by
    let _ := Ideal.Quotient.field n
    let ι : IsLocalRing.ResidueField B →+* S ⧸ n := Ideal.Quotient.lift _ ((Ideal.Quotient.mk n).comp (algebraMap B S)) fun b hb => Ideal.Quotient.eq_zero_iff_mem.mpr ((hker n hn b).mpr hb)
    have hq : (Q.map (IsLocalRing.residue B)).map ι = ((univ.val.map fun i => Ideal.Quotient.mk n (θ i)).map (X - C ·)).prod := by
      rw [Polynomial.map_map, show ι.comp (IsLocalRing.residue B) = (Ideal.Quotient.mk n).comp (algebraMap B S) from RingHom.ext fun _ => rfl, hmapn n, Multiset.map_map]; rfl
    rw [show a = ((Q.map (IsLocalRing.residue B)).map ι).rootMultiplicity (ι 0) from eq_rootMultiplicity_map ι.injective 0, map_zero, ← count_roots, hq, roots_multiset_prod_X_sub_C, Multiset.count_map, card_def, filter_val]
    exact congrArg Multiset.card (Multiset.filter_congr fun _ _ => (eq_comm.trans Ideal.Quotient.eq_zero_iff_mem).symm)
  have hcard' (n : Ideal S) (hn : n.IsMaximal) : (univ.filter (θ · ∉ n)).card = r := by
    have := card_filter_add_card_filter_not (s := univ) (θ · ∈ n); rw [hcard n hn, card_univ, Fintype.card_fin] at this; omega
  obtain ⟨F, hFS⟩ := exF Q θ hQ r
  have hmonic : F.Monic := monic_of_injective hinj (hFS ▸ monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _)
  let _ := Ideal.Quotient.field n2; let ψ : B →+* S ⧸ n2 := (Ideal.Quotient.mk n2).comp (algebraMap B S); let θb (i : Fin L.length) : S ⧸ n2 := Ideal.Quotient.mk n2 (θ i)
  have hψ (b : B) : ψ b = 0 ↔ b ∈ IsLocalRing.maximalIdeal B := Ideal.Quotient.eq_zero_iff_mem.trans (hker n2 hn2 b)
  let I0 := univ.filter (θ · ∉ n2); let c : S ⧸ n2 := ∏ i ∈ I0, θb i; let A : B := (-1) ^ r * Q.coeff a
  have hc0 : c ≠ 0 := prod_ne_zero_iff.mpr fun i hi => mt Ideal.Quotient.eq_zero_iff_mem.mp (mem_filter.mp hi).2
  have hI0mem : I0 ∈ powersetCard r univ := mem_powersetCard.mpr ⟨subset_univ _, hcard' n2 hn2⟩
  have hI0zero (I : Finset (Fin L.length)) (hIm : I ∈ powersetCard r univ) (hne : I ≠ I0) : ∏ i ∈ I, θb i = 0 := by
    obtain ⟨i, hiI, hiI0⟩ := not_subset.mp fun hs => hne (eq_of_subset_of_card_le hs (by rw [(mem_powersetCard.mp hIm).2, hcard' n2 hn2]))
    exact prod_eq_zero hiI (Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [I0] using hiI0))
  have hψA : ψ A = c := by
    have hv := Multiset.prod_X_sub_C_coeff (univ.val.map θb) (by simpa using hcard n2 hn2 ▸ (card_le_univ _).trans_eq (Fintype.card_fin _))
    rw [show ((univ.val.map θb).map (X - C ·)).prod = Q.map ψ by rw [hmapn n2, Multiset.map_map]; rfl, coeff_map, Multiset.card_map, card_val, card_univ, Fintype.card_fin, esymm_map_val, sum_eq_single I0 hI0zero fun h => absurd hI0mem h] at hv
    rw [show A = (-1) ^ r * Q.coeff a from rfl, map_mul, map_pow, map_neg, map_one, hv, ← mul_assoc, ← mul_pow]; simp [c]
  have hFψ : F.map ψ = (X - C c) * ∏ I ∈ (powersetCard r univ).erase I0, (X - C (∏ i ∈ I, θb i)) := by
    rw [← Polynomial.map_map, hFS, Polynomial.map_prod, ← mul_prod_erase _ _ hI0mem]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]; simp only [c, θb, I0, _root_.map_prod]
  have hder : (F.map ψ).derivative.eval c ≠ 0 := by
    rw [hFψ, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_prod]
    exact prod_ne_zero_iff.mpr fun I hI => by rw [hI0zero I (mem_erase.mp hI).2 (mem_erase.mp hI).1, sub_zero]; exact hc0
  have hev : F.eval A ∈ IsLocalRing.maximalIdeal B := by rw [← hψ, ← eval₂_at_apply, ← eval_map, hψA, hFψ]; simp
  have hunit : IsUnit (F.derivative.eval A) := by rw [← IsLocalRing.notMem_maximalIdeal]; rwa [← hψ, ← eval₂_at_apply, ← eval_map, hψA, ← derivative_map]
  obtain ⟨τ, hτ0, hτA⟩ := HenselianLocalRing.is_henselian F hmonic A hev hunit
  have hτm : τ ∉ IsLocalRing.maximalIdeal B := fun hm => hc0 (hψA ▸ (hψ A).mpr (by simpa using Ideal.sub_mem _ hm hτA))
  obtain ⟨I, hI, hIτ⟩ := prod_eq_zero_iff.mp (by rw [← eval_prod (x := algebraMap B S τ), ← hFS, eval_map, eval₂_at_apply, hτ0.eq_zero, map_zero])
  have hτI : algebraMap B S τ = ∏ i ∈ I, θ i := by rwa [eval_sub, eval_X, eval_C, sub_eq_zero] at hIτ
  have hIeq (n : Ideal S) (hn : n.IsMaximal) : I = univ.filter (θ · ∉ n) :=
    eq_of_subset_of_card_le (fun i hi => mem_filter.mpr ⟨mem_univ _, fun hin => hτm ((hker n hn τ).mp (hτI ▸ Ideal.mem_of_dvd n (dvd_prod_of_mem θ hi) hin))⟩) (by rw [(mem_powersetCard.mp hI).2, hcard' n hn])
  have hi0 : i0 ∈ I := by rw [hIeq n2 hn2]; exact mem_filter.mpr ⟨mem_univ _, h2⟩
  rw [hIeq n1 hn1] at hi0; exact (mem_filter.mp hi0).2 h1

private theorem ext_hom {B S C : Type} [CommRing B] [CommRing S] [IsDomain S] [Algebra B S] [Algebra.IsIntegral B S]
    (hinj : Function.Injective (algebraMap B S)) [Field C] [IsAlgClosed C] (f : B →+* C) : ∃ g : S →+* C, g.comp (algebraMap B S) = f := by
  let q := RingHom.ker f; have : q.IsPrime := RingHom.ker_isPrime f
  obtain ⟨P, hP, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S) q (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : P.LiesOver q := ⟨hc.symm⟩; let _ : Algebra (B ⧸ q) C := (RingHom.kerLift f).toAlgebra
  have : IsDomain (B ⧸ q) := Ideal.Quotient.isDomain q; have : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
  have : Module.IsTorsionFree (B ⧸ q) (S ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective _ _)
  have : Module.IsTorsionFree (B ⧸ q) C := Module.isTorsionFree_iff_algebraMap_injective.mpr f.kerLift_injective
  have : Algebra.IsIntegral (B ⧸ q) (S ⧸ P) := .tower_top B; have : Algebra.IsAlgebraic (B ⧸ q) (S ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let L : (S ⧸ P) →ₐ[B ⧸ q] C := IsAlgClosed.lift
  exact ⟨(L : (S ⧸ P) →+* C).comp (Ideal.Quotient.mk P), RingHom.ext fun b => L.commutes (Ideal.Quotient.mk q b)⟩

open Polynomial in
private theorem loc_hom {l : ℕ} [Fact (Nat.Prime l)] (κ : PadicAlgCl l) (hκ : 1 ≤ ‖κ‖) :
    ∃ h : ℤ_[l][X], h.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])) κ = 0 ∧ h.coeff 0 = 1 := by
  have hκ0 : κ ≠ 0 := by rintro rfl; norm_num at hκ
  have hm : (minpoly ℚ_[l] κ⁻¹).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hc : ∀ n, ‖(minpoly ℚ_[l] κ⁻¹).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).mp (show ‖κ⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ hκ)
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (show minpoly ℚ_[l] κ⁻¹ ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) by rw [lifts_iff_coeff_lifts]; exact fun n => ⟨⟨_, hc n⟩, rfl⟩) hm
  refine ⟨q.reverse, ?_, q.coeff_zero_reverse.trans hqm⟩
  let _ : Invertible κ⁻¹ := invertibleOfNonzero (inv_ne_zero hκ0)
  let ψ := (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])
  have h1 := q.eval₂_reverse_mul_pow ψ κ⁻¹
  rw [invOf_eq_inv, inv_inv, show q.eval₂ ψ κ⁻¹ = 0 by rw [← eval₂_map, hq]; exact minpoly.aeval _ _] at h1
  exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ (inv_ne_zero hκ0))

set_option linter.unusedVariables false in set_option linter.overlappingInstances false in
theorem UpperTheory.Reformulated.B.MajorantSquareBound.spl_near :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {O B : Type}
    [inst_1 : CommRing O] [inst_2 : Algebra ℤ_[l] O] [inst_3 : Algebra O (PadicAlgCl l)]
    [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [inst_5 : CommRing B] [IsDomain B] [HenselianLocalRing B]
    [inst_8 : Algebra O B] (x y : B →ₐ[O] PadicAlgCl l) (d : O),
    (Algebra.algebraMap O (PadicAlgCl l) : O → PadicAlgCl l) d ≠ (0 : PadicAlgCl l) →
      ∀ (t : B),
        (x : B → PadicAlgCl l) t = (0 : PadicAlgCl l) →
          ∀ (v : FractionRing B),
            IsIntegral B v →
              (Algebra.algebraMap B (FractionRing B) : B → FractionRing B) ((Algebra.algebraMap O B : O → B) d) * v =
                  (Algebra.algebraMap B (FractionRing B) : B → FractionRing B) t →
                ∀ (κ : PadicAlgCl l),
                  (Algebra.algebraMap O (PadicAlgCl l) : O → PadicAlgCl l) d * κ = (y : B → PadicAlgCl l) t →
                    ‖κ‖ < (1 : ℝ) := by
  intro l _ O B _ _ _ _ _ _ _ _ x y d hd t hxt v hv hdv κ hκ
  by_contra! hκ1
  let K := FractionRing B; let S := integralClosure B (AlgebraicClosure K)
  have : IsLocalRing S := isLocalRing_integralClosure
  have hinj : Function.Injective (algebraMap B S) := fun a b h =>
    IsFractionRing.injective B K ((algebraMap K (AlgebraicClosure K)).injective (congrArg Subtype.val h))
  obtain ⟨gx, hgx⟩ := ext_hom hinj (x : B →+* PadicAlgCl l); obtain ⟨gy, hgy⟩ := ext_hom hinj (y : B →+* PadicAlgCl l)
  have ex (b : B) : gx (algebraMap B S b) = x b := DFunLike.congr_fun hgx b
  have ey (b : B) : gy (algebraMap B S b) = y b := DFunLike.congr_fun hgy b
  let vS : S := ⟨algebraMap K _ v, hv.algebraMap⟩
  have hS : algebraMap B S (algebraMap O B d) * vS = algebraMap B S t := Subtype.ext <| by
    have := congrArg (algebraMap K (AlgebraicClosure K)) hdv
    rwa [map_mul, ← IsScalarTower.algebraMap_apply B K, ← IsScalarTower.algebraMap_apply B K] at this
  have h1 : gx vS = 0 := (mul_eq_zero.mp (by simpa [ex, x.commutes, hxt] using congrArg gx hS)).resolve_left hd
  have h2 : gy vS = κ := mul_left_cancel₀ hd (by simpa [ey, y.commutes, ← hκ] using congrArg gy hS)
  obtain ⟨h, hh0, hh1⟩ := loc_hom κ hκ1
  let φ : ℤ_[l] →+* S := (algebraMap B S).comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))
  have hφ : gy.comp φ = (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l]) := by
    ext a; simp only [φ, RingHom.comp_apply, ey, y.commutes]
    rw [← IsScalarTower.algebraMap_apply ℤ_[l] O (PadicAlgCl l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  have mem_max (z : S) (g : S →+* PadicAlgCl l) (hz : g z = 0) : z ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu => not_isUnit_zero (hz ▸ hu.map g)
  have hmem := Ideal.sub_mem _ (mem_max (h.eval₂ φ vS) gy (by rw [Polynomial.hom_eval₂, hφ, h2, hh0])) (Ideal.mul_mem_left _ (h.divX.eval₂ φ vS) (mem_max vS gx h1))
  rw [show h.eval₂ φ vS = h.divX.eval₂ φ vS * vS + 1 by
    conv_lhs => rw [← h.divX_mul_X_add, hh1]; simp [Polynomial.eval₂_add, Polynomial.eval₂_mul], add_sub_cancel_left] at hmem
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal S).ne_top hmem
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MajorantSquareBound =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MajorantSquareBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.FieldTheory.Galois.Profinite\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

namespace UpperTheory.V.Loc

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H] (f : R →+* K)

private theorem spl_rep (r : H →* M4 R) (g : H) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem spl_smul (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp

private theorem spl_adj (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem spl_gsp {ν : R} {X : M4 R} (h : IsGSp ν X) : IsGSp (f ν) (f.mapMatrix X) := by
  unfold IsGSp at *
  rw [spl_adj, ← map_mul, h, spl_smul, map_one]

private theorem spl_prj (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  unfold prj
  have h : ∀ p : Polynomial R,
      Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, spl_smul, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem spl_ord {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r : H →* M4 R} (h : Ord I ps s₀ r) :
    Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [spl_rep, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · intro g i j hij
    rw [spl_rep, spl_rep, spl_prj f (fun a => ps a s₀), spl_prj f (fun a => ps a s₀), ← map_mul, ← map_mul,
      h.stable g i j hij, map_zero]
  · intro s hs i
    rw [spl_rep, spl_rep, spl_prj f (fun a => ps a s₀), ← map_one f.mapMatrix, ← spl_smul, ← map_sub, ← map_mul,
      ← map_mul, h.inert s hs i, map_zero]

private theorem spl_tr (c : Fin 4 → R) (X Y : M4 R) (i : Fin 4) :
    (prj (fun a => f (c a)) (f.mapMatrix X) i * f.mapMatrix Y).trace = f (prj c X i * Y).trace := by
  rw [spl_prj, ← map_mul, RingHom.mapMatrix_apply, AddMonoidHom.map_trace]

private theorem spl_tr_diag (c a : Fin 4 → R) (i : Fin 4) :
    (prj c (Matrix.diagonal c) i * Matrix.diagonal a).trace = (∏ j ∈ Finset.univ.erase i, (c i - c j)) * a i := by
  have h : prj c (Matrix.diagonal c) i = Matrix.diagonal fun b => ∏ j ∈ Finset.univ.erase i, (c b - c j) := by
    unfold prj
    have h1 := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom (n := Fin 4) (α := R) R) c
      (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (c j)))
    rw [Matrix.diagonalAlgHom_apply, Matrix.diagonalAlgHom_apply] at h1
    rw [h1]
    congr 1
    funext b
    simp [map_prod]
  rw [h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Finset.sum_eq_single i]
  · intro b _ hb
    rw [Finset.prod_eq_zero (i := b) (by simp [hb]) (sub_self _), zero_mul]
  · simp

private theorem spl_adj_mul (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev] <;> ring

private theorem spl_adj_one : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem spl_conj {ν : R} {X : M4 R} (h : IsGSp ν X) (u v : M4 R) (hv : v * u = 1) :
    adj (u * X * v) * (adj v * v) * (u * X * v) = ν • (adj v * v) := by
  have h1 : adj u * adj v = 1 := by
    rw [← spl_adj_mul, hv, spl_adj_one]
  unfold IsGSp at h
  rw [spl_adj_mul, spl_adj_mul]
  calc _ = adj v * (adj X * (adj u * adj v) * (v * u) * X) * v := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, hv, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

private theorem spl_adj_unit (u : (M4 R)ˣ) : IsUnit (adj (u : M4 R)) :=
  IsUnit.of_mul_eq_one (adj ((u⁻¹ : (M4 R)ˣ) : M4 R)) (by rw [← spl_adj_mul, Units.inv_mul, spl_adj_one])

end Gen

section Fld

variable {K : Type} [Field K]

private theorem spl_gram {ν : K} {M A : M4 K} (hM : ∀ i j, j < i → M i j = 0) (h : adj M * A * M = ν • A)
    (hc : ∀ i j : Fin 4, j < i → M i.rev i.rev * M j j ≠ ν) : ∀ i j, j < i → A i j = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have m10 := hM 1 0 (by decide)
  have m20 := hM 2 0 (by decide)
  have m30 := hM 3 0 (by decide)
  have m21 := hM 2 1 (by decide)
  have m31 := hM 3 1 (by decide)
  have m32 := hM 3 2 (by decide)
  have k : ∀ {a b x : K}, a ≠ b → a * x = b * x → x = 0 := fun hab hx => by
    by_contra h0
    exact hab (mul_right_cancel₀ h0 hx)
  have e30 := e 3 0
  have e20 := e 2 0
  have e10 := e 1 0
  have e31 := e 3 1
  have e21 := e 2 1
  have e32 := e 3 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, m10, m20, m30, m21, m31, m32] at e30 e20 e10 e31 e21 e32
  have a30 : A 3 0 = 0 := k (hc 3 0 (by decide)) (by show M 0 0 * M 0 0 * _ = _; linear_combination e30)
  rw [a30] at e20 e10 e31 e21 e32
  have a20 : A 2 0 = 0 := k (hc 2 0 (by decide)) (by show M 1 1 * M 0 0 * _ = _; linear_combination e20)
  have a31 : A 3 1 = 0 := k (hc 3 1 (by decide)) (by show M 0 0 * M 1 1 * _ = _; linear_combination e31)
  simp only [a20, a31] at e10 e21 e32
  have a10 : A 1 0 = 0 := k (hc 1 0 (by decide)) (by show M 2 2 * M 0 0 * _ = _; linear_combination e10)
  have a21 : A 2 1 = 0 := k (hc 2 1 (by decide)) (by show M 1 1 * M 1 1 * _ = _; linear_combination e21)
  have a32 : A 3 2 = 0 := k (hc 3 2 (by decide)) (by show M 0 0 * M 2 2 * _ = _; linear_combination e32)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

private theorem spl_dual {ν : K} {M A : M4 K} (hM : ∀ i j, j < i → M i j = 0) (hA : ∀ i j, j < i → A i j = 0)
    (hu : IsUnit A) (h : adj M * A * M = ν • A) (i : Fin 4) : M i.rev i.rev * M i i = ν := by
  have hA' : A.BlockTriangular id := fun i j h => hA i j h
  have hM' : M.BlockTriangular id := fun i j h => hM i j h
  have hN : (adj M).BlockTriangular id := fun i j h => by
    rw [adj_apply, hM j.rev i.rev (Fin.rev_lt_rev.2 h), smul_zero]
  have hd : ∀ {X Y : M4 K}, X.BlockTriangular id → Y.BlockTriangular id → (X * Y) i i = X i i * Y i i := by
    intro X Y hX hY
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hX h, zero_mul]
      · rw [hY h, mul_zero]
    · simp
  have h0 : A i i ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det A).1 hu).ne_zero
    rw [Matrix.det_of_upperTriangular hA'] at this
    exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)
  have e := congrFun (congrFun h i) i
  have hs : ∀ i, sgn i * sgn i = 1 := by decide
  rw [hd (hN.mul hA') hM', hd hN hA', adj_apply, hs, one_smul, Matrix.smul_apply, smul_eq_mul] at e
  exact mul_right_cancel₀ h0 (by linear_combination e)

private theorem spl_int {B : Type} [CommRing B] [Algebra B K] (X : M4 B) (u : (M4 K)ˣ)
    (hM : ∀ i j, j < i → ((u : M4 K) * (algebraMap B K).mapMatrix X * (u⁻¹ : (M4 K)ˣ)) i j = 0) (i : Fin 4) :
    IsIntegral B (((u : M4 K) * (algebraMap B K).mapMatrix X * (u⁻¹ : (M4 K)ˣ)) i i) := by
  refine ⟨X.charpoly, X.charpoly_monic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map, ← RingHom.mapMatrix_apply,
    ← Matrix.charpoly_units_conj u, ← Matrix.coe_units_inv, Matrix.charpoly_of_upperTriangular _ (fun i j h => hM i j h),
    Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

end Fld


private theorem spl_red {l : ℕ} [Fact l.Prime] {O B H : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing B] [IsDomain B] [HenselianLocalRing B]
    [Algebra O B] [Group H] (hO : Function.Injective (algebraMap O (PadicAlgCl l))) {I : Subgroup H}
    {ps : Fin 4 → H → O} {s₀ : H} (hinj : Function.Injective fun i => ps i s₀) {ρ : H →* M4 B}
    (hρ : Ord I (fun i g => algebraMap O B (ps i g)) s₀ ρ) (x : B →ₐ[O] O)
    (hx : ∀ g a b, x (ρ g a b) = Matrix.diagonal (fun i => ps i g) a b) (y : B →ₐ[O] PadicAlgCl l) (i : Fin 4) (g : H)
    (κ : PadicAlgCl l)
    (hκ : (∏ j ∈ Finset.univ.erase i, (algebraMap O _ (ps i s₀) - algebraMap O _ (ps j s₀))) * κ =
      (prj (fun a => algebraMap O _ (ps a s₀)) (mapRep (y : B →+* PadicAlgCl l) ρ s₀) i *
        mapRep (y : B →+* PadicAlgCl l) ρ g).trace) : ‖κ - algebraMap O _ (ps i g)‖ < 1 := by
  let d : O := ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)
  let t : B := (prj (fun a => algebraMap O B (ps a s₀)) (ρ s₀) i * ρ g).trace
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun e => (Finset.mem_erase.1 hj).1 (hinj e).symm
  have hB : Function.Injective (algebraMap O B) := fun a b e => by simpa using congrArg x e
  have hxt : x t = d * ps i g := by
    have h1 := spl_tr (x : B →+* O) (fun a => algebraMap O B (ps a s₀)) (ρ s₀) (ρ g) i
    have h2 : ∀ g, (x : B →+* O).mapMatrix (ρ g) = Matrix.diagonal fun i => ps i g := fun g => Matrix.ext (hx g)
    simp only [h2, RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [spl_tr_diag] at h1
    exact h1.symm
  have hyt : algebraMap O _ d * κ = y t := by
    have h1 := spl_tr (y : B →+* PadicAlgCl l) (fun a => algebraMap O B (ps a s₀)) (ρ s₀) (ρ g) i
    simp only [RingHom.coe_coe, AlgHom.commutes] at h1
    rw [← h1, map_prod]
    simp only [map_sub]
    exact hκ
  obtain ⟨u, k, h1, h2, -, h4⟩ := ordFlag I (FractionRing B) _ s₀ _
    (fun a b e => hinj (hB (IsFractionRing.injective B (FractionRing B) e))) (spl_ord (algebraMap B (FractionRing B)) hρ)
  have hint : IsIntegral B (k i g : FractionRing B) := h2 g i ▸ spl_int (ρ g) u (h1 g) i
  have hk : algebraMap B (FractionRing B) (algebraMap O B d) * k i g = algebraMap B _ t := by
    rw [← spl_tr (algebraMap B (FractionRing B)), map_prod, map_prod]
    simp only [map_sub]
    exact h4 i g
  refine _root_.UpperTheory.Reformulated.B.MajorantSquareBound.spl_near ((Algebra.ofId O _).comp x) y d ((map_ne_zero_iff _ hO).2 hd) (t - algebraMap O B (d * ps i g)) ?_
    (k i g - algebraMap B _ (algebraMap O B (ps i g))) (hint.sub isIntegral_algebraMap) ?_ _ ?_
  · rw [AlgHom.comp_apply, map_sub, hxt, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
  · rw [mul_sub, hk, map_sub, map_mul, map_mul]
  · rw [mul_sub, hyt, map_sub, AlgHom.commutes, map_mul]

private theorem spl_cont {X R K : Type} [TopologicalSpace X] [CommRing R] [NormedRing K] (I : Ideal R) (y : R →+* K)
    {a : ℝ} (h1 : a < 1) (h0 : 0 ≤ a) (h : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n) {f : X → R} (hf : AdicCont I f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε h1
  filter_upwards [(hf k).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact (h k _ (Ideal.Quotient.eq.1 hg')).trans_lt hk

private theorem spl_bar {l : ℕ} [Fact l.Prime] (c : Coef l) {a b : c.O} {z : PadicAlgCl l} (ha : ‖z - a‖ < 1)
    (hb : ‖z - b‖ < 1) : residue c.O a = residue c.O b := by
  obtain ⟨-, t, -, -, ht⟩ := (coPt c c.O).1 (Algebra.ofId _ _)
  have h1 : ‖((a - b : c.O) : PadicAlgCl l)‖ < 1 := by
    have : ((a - b : c.O) : PadicAlgCl l) = (z - b) + -(z - a) := by push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hb (by rwa [norm_neg]))
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 : ‖(w : PadicAlgCl l)‖ ≤ 1 := by simpa using ht 0 w (by simp)
  have h3 : ‖((a - b : c.O) : PadicAlgCl l)‖ * ‖(w : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← MulMemClass.coe_mul, hw, OneMemClass.coe_one, norm_one]
  nlinarith [norm_nonneg ((a - b : c.O) : PadicAlgCl l), norm_nonneg (w : PadicAlgCl l)]

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.spPtL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (r : D.Gp l →* M4 (PadicAlgCl l)), PtOn D D.condL r → ∃ (h : (M4 (PadicAlgCl l))ˣ) (κ : Fin 4 → D.Gp l →* (PadicAlgCl l)ˣ), FlagIn r h κ ∧ (∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → (κ i s : PadicAlgCl l) = ((D.ps i s : c.Oˣ) : c.O)) ∧ (∀ i g, ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.Oˣ) : c.O)‖ < 1) ∧ (∀ g : D.Gp l, ((κ 0 g * κ 3 g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((D.th g : c.Oˣ) : c.O) ∧ ((κ 1 g * κ 2 g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((D.th g : c.Oˣ) : c.O)) ∧ (∀ i, Continuous fun g => (κ i g : PadicAlgCl l)) ∧ ∀ i j, i ≠ j → ∀ U : Subgroup (D.Gp l), IsOpen (U : Set (D.Gp l)) → (∃ g ∈ U, (g : G ℚ Ω) = D.sg l) → ∃ g ∈ U, (κ i g : PadicAlgCl l) ≠ (κ j g : PadicAlgCl l) * ((chiO ℚ Ω l c.O g : c.Oˣ) : c.O) := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, _, _, _, ρ', y', ⟨B, _, _, _, _, ρ, hρ, ⟨x, hx⟩, y₀, rfl⟩, rfl⟩ := hr
  obtain ⟨-, hT, -, hwt, -, hrev, hinj, -⟩ := facts D hD
  let y : B →ₐ[c.O] PadicAlgCl l := y'.comp y₀
  have er : mapRep (y' : R →+* PadicAlgCl l) (ρ.map y₀).hom = mapRep (y : B →+* PadicAlgCl l) ρ.hom := rfl
  rw [er]
  have hy : ∀ a : c.O, (y : B →+* PadicAlgCl l) (algebraMap c.O B a) = algebraMap c.O _ a := fun a => y.commutes a
  have hO : Function.Injective (algebraMap c.O (PadicAlgCl l)) := Subtype.val_injective
  have hord := spl_ord (y : B →+* PadicAlgCl l) hρ.2
  simp only [hy] at hord
  have hgsp : ∀ g : D.Gp l, IsGSp (algebraMap c.O _ (D.th g)) (mapRep (y : B →+* PadicAlgCl l) ρ.hom g) := fun g => by
    have h := spl_gsp (y : B →+* PadicAlgCl l) (hρ.1 g)
    rwa [hy] at h
  obtain ⟨u, κ, h1, h2, h3, h4⟩ := ordFlag _ (PadicAlgCl l) _ D.s0 _ (fun a b e => hinj (hO e)) hord
  haveI : HenselianLocalRing B := GlobalTheory.henselianLocalRing_of_henselianRing B
  have hs0 : D.s0 ∈ (D.Ip l).subgroupOf (D.Gp l) := hD.decompSigma_mem.1.1
  have hred : ∀ i (g : D.Gp l), ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.Oˣ) : c.O)‖ < 1 := fun i g =>
    spl_red hO (ps := fun i (g : D.Gp l) => (D.ps i g : c.O)) hinj hρ.2 x hx y i g _ (h4 i g)
  have hdual : ∀ (g : D.Gp l) (i : Fin 4), (κ i.rev g : PadicAlgCl l) * κ i g = algebraMap c.O _ (D.th g) := by
    intro g i
    have hA := spl_gram (h1 D.s0) (spl_conj (hgsp D.s0) _ _ u.inv_mul) fun i j hij e => by
      rw [h2, h2, h3 _ _ hs0, h3 _ _ hs0, ← map_mul, ← hrev i, MonoidHom.mul_apply, mul_comm (D.ps i _), Units.val_mul] at e
      exact hij.ne (hinj ((Units.mul_right_inj _).1 (hO e)))
    rw [← h2, ← h2]
    exact spl_dual (h1 g) hA ((spl_adj_unit u⁻¹).mul (u⁻¹).isUnit) (spl_conj (hgsp g) _ _ u.inv_mul) i
  refine ⟨u⁻¹, κ, fun g => ⟨h1 g, h2 g⟩, fun i s hs => h3 i s hs, hred, fun g => ⟨hdual g 3, hdual g 2⟩, fun i => ?_,
    fun i j hij U hU ⟨g, hg, hgs⟩ => ?_⟩
  · obtain ⟨-, a, a1, a0, ha⟩ := (coPt c B).1 y
    have hc : Continuous fun g => mapRep (y : B →+* PadicAlgCl l) ρ.hom g :=
      continuous_matrix fun a b => spl_cont _ (y : B →+* PadicAlgCl l) a1 a0 ha (ρ.cont a b)
    simp only [← h2]
    exact ((continuous_const.matrix_mul hc).matrix_mul continuous_const).matrix_elem i i
  · by_contra hn
    push Not at hn
    have hlam : lamW i ≠ lamW j := by
      haveI : CompactSpace (D.Gp l) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
      haveI := Subgroup.quotient_finite_of_isOpen U hU
      haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      obtain ⟨n, hn0, -, hnU⟩ := U.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero D.s0
      have e := hn _ hnU
      have hm : ((D.s0 ^ n : D.Gp l) : G ℚ Ω) ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker := pow_mem hD.decompSigma_mem n
      rw [h3 i _ hm.1.1, h3 j _ hm.1.1, hwt i _ hm, hwt j _ hm] at e
      have e1 : chiO ℚ Ω l c.O (D.s0 ^ n : D.Gp l) ^ D.wts4 i = chiO ℚ Ω l c.O (D.s0 ^ n : D.Gp l) ^ (D.wts4 j + 1) := by
        apply Units.ext
        apply hO
        rw [e, pow_succ, Units.val_mul, map_mul]
        rfl
      have hZ : Function.Injective (algebraMap ℤ_[l] c.O) :=
        Function.Injective.of_comp (f := algebraMap c.O (PadicAlgCl l)) (by
          rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l]]
          exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
      have hf : ¬ IsOfFinOrder (chiO ℚ Ω l c.O (D.s0 ^ n : D.Gp l)) := fun hf => hD.decompSigma_ord (by
        have h5 := ((Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hZ).isOfFinOrder_iff).1 hf
        rw [SubgroupClass.coe_pow, map_pow] at h5
        exact h5.of_pow hn0.ne')
      have e2 := injective_pow_iff_not_isOfFinOrder.2 hf e1
      have := hD.two_le
      fin_cases i <;> fin_cases j <;> simp [Raw.wts4, lamW] at e2 ⊢ <;> omega
    have e := hn g hg
    have e1 : chiO ℚ Ω l c.O g = 1 := by
      rw [hgs, chiO, MonoidHom.comp_apply, hD.sg_cyc, map_one]
    rw [e1, Units.val_one, OneMemClass.coe_one, mul_one] at e
    refine (hT l (Finset.mem_insert_self _ _)).2.2 i j hlam ?_
    rw [← hgs]
    exact spl_bar c (hred i g) (e ▸ hred j g)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit =====
