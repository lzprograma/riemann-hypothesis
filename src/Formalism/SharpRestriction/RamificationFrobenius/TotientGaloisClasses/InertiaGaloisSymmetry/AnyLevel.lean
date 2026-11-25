module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfCharFrame
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSym
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfChar
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Mathlib.Algebra.Order.Star.Int

@[expose] public section

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem unitsMap_unitOfCoprime {M N : ℕ} (h : M ∣ N) (a : ℕ) (ha : Nat.Coprime a N) :
    ZMod.unitsMap h (ZMod.unitOfCoprime a ha) = ZMod.unitOfCoprime a (ha.coprime_dvd_right h) := by
  ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

theorem HostRaw.art_eq_of_prim_eq {φ : Frame} (H : HostRaw φ) {θ θ' : φ.Char} (h : H.prim θ = H.prim θ')
    (u : (ZMod H.condN)ˣ) : θ (H.art u) = θ' (H.art u) := by
  have h1 := (H.isPrimOf_prim θ).2 _ (ZMod.val_coe_unit_coprime u)
  have h2 := ((H.isPrimOf_iff θ' _).mpr h).2 _ (ZMod.val_coe_unit_coprime u)
  have h3 := h1.symm.trans h2
  rw [HostRaw.dirAt, HostRaw.dirAt, ZMod.natCast_zmod_val, H.dir_unit, H.dir_unit] at h3
  exact Units.ext h3

namespace EvenGrp

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def ann : Subgroup (ZMod M)ˣ := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).symm (OrderDual.toDual Ξ)

theorem mem_ann (u : (ZMod M)ˣ) : u ∈ ann Ξ ↔ ∀ χ ∈ Ξ, χ u = 1 := by
  simp [ann]

theorem mem_iff (χ : DirichletCharacter ℂ M) : χ ∈ Ξ ↔ ∀ u ∈ ann Ξ, χ u = 1 := by
  have h1 := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).apply_symm_apply (OrderDual.toDual Ξ)
  have h2 : χ ∈ Ξ ↔ χ ∈ OrderDual.ofDual ((MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ) (ann Ξ)) := by
    simp only [ann, h1, OrderDual.ofDual_toDual]
  rw [h2]
  generalize ann Ξ = S
  simp

abbrev B : Type := (ZMod M)ˣ ⧸ ann Ξ

theorem card_B : Nat.card (B Ξ) = Nat.card Ξ := by
  rw [← MulChar.card_subgroupOrderIsoSubgroupMulChar (R := ℂ), ann, OrderIso.apply_symm_apply]
  rfl

instance neZero_lcm : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩

def xiW : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* B Ξ := (QuotientGroup.mk' _).comp (ZMod.unitsMap (Nat.dvd_lcm_right _ _))

theorem xiW_surj : Function.Surjective (xiW Ξ e) := by
  intro b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (ann Ξ) b
  obtain ⟨c, rfl⟩ := ZMod.unitsMap_surjective (Nat.dvd_lcm_right (2 ^ (e + 2)) M) a
  exact ⟨c, rfl⟩

def Good (m : ℕ) : Prop := m ∣ Nat.lcm (2 ^ (e + 2)) M ∧ 2 ^ (e + 2) ∣ m ∧
  ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ, (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val ≡ 1 [MOD m] → xiW Ξ e u = 1

theorem exists_good : ∃ m, Good Ξ e m := by
  refine ⟨Nat.lcm (2 ^ (e + 2)) M, dvd_rfl, Nat.dvd_lcm_left _ _, fun u hu => ?_⟩
  have h1 : ((u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val : ZMod (Nat.lcm (2 ^ (e + 2)) M)) =
      ((1 : ℕ) : ZMod (Nat.lcm (2 ^ (e + 2)) M)) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  have h2 : u = 1 := Units.ext (by rw [h1, Units.val_one])
  rw [h2, map_one]


open Classical in
def QS : ℕ := Nat.find (exists_good Ξ e)

open Classical in
theorem good_QS : Good Ξ e (QS Ξ e) := Nat.find_spec (exists_good Ξ e)

open Classical in
theorem not_good {m : ℕ} (h : m < QS Ξ e) : ¬ Good Ξ e m := Nat.find_min (exists_good Ξ e) h

theorem QS_dvd : QS Ξ e ∣ Nat.lcm (2 ^ (e + 2)) M := (good_QS Ξ e).1

theorem QS_dvd_mul : QS Ξ e ∣ 2 ^ (e + 2) * M :=
  (QS_dvd Ξ e).trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))

theorem QS_pos : 0 < QS Ξ e := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have h1 := QS_dvd Ξ e
  rw [h, zero_dvd_iff] at h1
  exact (NeZero.ne _) h1

instance neZero_QS : NeZero (QS Ξ e) := ⟨(QS_pos Ξ e).ne'⟩

def xi : (ZMod (QS Ξ e))ˣ →* B Ξ :=
  (ZMod.unitsMap (QS_dvd Ξ e)).liftOfSurjective (ZMod.unitsMap_surjective _)
    ⟨xiW Ξ e, fun u hu => (good_QS Ξ e).2.2 u ((unitsMap_eq_one_iff _ u).mp hu)⟩

theorem xi_unitsMap (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) : xi Ξ e (ZMod.unitsMap (QS_dvd Ξ e) u) = xiW Ξ e u :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem xi_surj : Function.Surjective (xi Ξ e) := by
  intro b
  obtain ⟨u, rfl⟩ := xiW_surj Ξ e b
  exact ⟨_, xi_unitsMap Ξ e u⟩

variable (hev : ∀ χ ∈ Ξ, χ.Even)

def data : EvenData where
  e := e
  m := QS Ξ e
  m_pos := QS_pos Ξ e
  tower := (good_QS Ξ e).2.1
  B := B Ξ
  ξ := xi Ξ e
  even := by
    rw [← D7.unitsMap_neg_one (QS_dvd Ξ e), xi_unitsMap]
    show ((ZMod.unitsMap _ (-1) : (ZMod M)ˣ) : B Ξ) = 1
    rw [D7.unitsMap_neg_one, QuotientGroup.eq_one_iff, mem_ann]
    exact hev

def frame : Frame := (data Ξ e hev).frame

theorem dvd_of_dvd_QS {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ QS Ξ e) : l ∣ M := by
  rcases (Nat.Prime.dvd_mul hl).mp (h.trans (QS_dvd_mul Ξ e)) with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h1)) h2
  · exact h1


theorem exact_data_aux (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧
      ((((QuotientGroup.mk' _ : (ZMod (2 ^ (e + 2)))ˣ →* HGrp e).comp (ZMod.unitsMap (good_QS Ξ e).2.1)).prod (xi Ξ e)) v) ≠ 1 := by
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self (QS_pos Ξ e) hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    refine not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩
    by_contra h3
    refine hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩
    rw [← xi_unitsMap]
    exact congrArg Prod.snd h4
  · obtain ⟨c, hc⟩ := (good_QS Ξ e).2.1
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l := Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_modEq _ _
    refine ⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩
    · rw [hdiv]
      simp [Nat.ModEq]
    · have h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1 :=
        congrArg Prod.fst h4
      rw [unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
        Units.val_one, Nat.cast_add, Nat.cast_one] at h5
      rcases h5 with h5 | h5
      · refine h2 ?_
        rw [hdiv, ← ZMod.natCast_eq_zero_iff]
        linear_combination h5
      · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
          linear_combination h5
        have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
        have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
        omega

theorem exact_data (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e hev).eta v ≠ 1 :=
  exact_data_aux Ξ e he l hl hd

def thetaB (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : B Ξ →* ℂˣ :=
  QuotientGroup.lift (ann Ξ) χ.toUnitHom fun u hu =>
    Units.ext ((MulChar.coe_toUnitHom χ u).trans ((mem_ann Ξ u).mp hu χ hχ))

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

include hH hc in
theorem coprime_QS : Nat.Coprime (QS Ξ e) (q * d) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  have h2 : Nat.Coprime 2 (q * d) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
    · exact (Nat.coprime_primes Nat.prime_two hd).mpr (by omega)
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul_left (Nat.Coprime.pow_left _ h2) hc)

def host : HostRaw (frame Ξ e hev) :=
  (data Ξ e hev).host hH (coprime_QS Ξ e hH hc) he fun l hl h2 h => hs l hl h2 (dvd_of_dvd_QS Ξ e hl h2 h)

theorem exact : (host Ξ e hev hH hc he hs).Exact := by
  apply (data Ξ e hev).exact
  intro l hl hd
  exact exact_data Ξ e hev (by omega) l hl hd

end Host

end EvenGrp

namespace AnyGrp

open EvenGrp (B QS QS_pos good_QS QS_dvd QS_dvd_mul xi xi_unitsMap not_good thetaB coprime_QS dvd_of_dvd_QS)

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def data : ModData where
  e := e
  m := QS Ξ e
  m_pos := QS_pos Ξ e
  tower := (good_QS Ξ e).2.1
  B := B Ξ
  ξ := xi Ξ e

abbrev frame : Frame := (data Ξ e).frame

theorem frame_e : (frame Ξ e).e = e := rfl

theorem o_eq : (frame Ξ e).o = Nat.card Ξ := by
  show (data Ξ e).frame.o = _
  rw [ModData.o_eq]
  show Nat.card (xi Ξ e).range = _
  rw [MonoidHom.range_eq_top.mpr (EvenGrp.xi_surj Ξ e), Subgroup.card_top]
  exact EvenGrp.card_B Ξ

theorem twoGroup (h : ∃ j : ℕ, Nat.card Ξ = 2 ^ j) : (frame Ξ e).TwoGroup := by
  obtain ⟨j, hj⟩ := h
  apply ModData.twoGroup
  refine ⟨j, fun u => ?_⟩
  have h2 : Nat.card (B Ξ) = 2 ^ j := (EvenGrp.card_B Ξ).trans hj
  rw [← h2]
  exact pow_card_eq_one'

theorem QS_le (h : 4 * M ≤ 2 ^ e) : QS Ξ e ≤ (frame Ξ e).ord ^ 2 := by
  have h1 := Nat.le_of_dvd (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne M))) (QS_dvd_mul Ξ e)
  have h2 : 2 ^ e ≤ (frame Ξ e).ord := (frame Ξ e).two_pow_le_ord
  calc QS Ξ e ≤ 2 ^ e * (4 * M) := by rw [pow_add] at h1; linarith
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_left _ h
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul h2 h2


theorem exact_data (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e).eta v ≠ 1 :=
  EvenGrp.exact_data_aux Ξ e he l hl hd

def thetaA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).MA →* ℂˣ := (thetaB Ξ χ hχ).comp (data Ξ e).xiA

def theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).Char :=
  (thetaA Ξ e χ hχ).comp (MonoidHom.snd G0 (frame Ξ e).MA * (data Ξ e).w.comp (frame Ξ e).chQ)

theorem theta_mem (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : theta Ξ e χ hχ ∈ (frame Ξ e).Xp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · have h1 : (frame Ξ e).iota s * (data Ξ e).w 1 = (frame Ξ e).iota s :=
      (congrArg ((frame Ξ e).iota s * ·) (map_one (data Ξ e).w)).trans (mul_one _)
    exact (congrArg (thetaA Ξ e χ hχ) h1).trans
      ((congrArg (thetaB Ξ χ hχ) (((data Ξ e).mem_cusp_forms_iff_automorphic_compact s).mp hs)).trans (map_one _))
  · exact (congrArg (thetaA Ξ e χ hχ) ((one_mul _).trans (map_one (data Ξ e).w))).trans (map_one _)

theorem thetaA_toA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) =
      χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) :=
  congrArg (thetaB Ξ χ hχ) (((data Ξ e).xiA_toA _).trans (xi_unitsMap Ξ e u))

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

def host : HostRaw (frame Ξ e) :=
  (data Ξ e).host hH (coprime_QS Ξ e hH hc) he fun l hl h2 h => hs l hl h2 (dvd_of_dvd_QS Ξ e hl h2 h)

theorem host_q : (host Ξ e hH hc he hs).q = q := rfl
theorem host_d : (host Ξ e hH hc he hs).d = d := rfl
theorem host_QS : (host Ξ e hH hc he hs).QS = QS Ξ e := rfl

theorem psQ : (host Ξ e hH hc he hs).PsQ := by
  unfold host
  apply ModData.psQ

theorem exact : (host Ξ e hH hc he hs).Exact := by
  unfold host
  apply ModData.exact
  intro l hl hd
  exact exact_data Ξ e (by omega) l hl hd

theorem muPM (hq : q ≠ 3) (hmu : ∀ k : ℕ, k ∣ QS Ξ e →
    (∀ v : (ZMod (QS Ξ e))ˣ, (data Ξ e).eta v = 1 → (v : ZMod (QS Ξ e)).val ≡ 1 [MOD k]) → k ∣ 2) :
    (host Ξ e hH hc he hs).MuPM := by
  unfold host
  apply ModData.muPM (hq := hq) (hmu := hmu)


theorem exists_sqq : ∃ s : (host Ξ e hH hc he hs).E, s ^ 2 = -((host Ξ e hH hc he hs).q : (host Ξ e hH hc he hs).E) ∧
    ∀ σ : (host Ξ e hH hc he hs).E ≃ₐ[ℚ] (host Ξ e hH hc he hs).E,
      σ s = (((((host Ξ e hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (host Ξ e hH hc he hs).E) * s := by
  unfold host
  apply ModData.exists_sqq

theorem theta_art (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (QS Ξ e * q * d))ˣ) :
    theta Ξ e χ hχ ((host Ξ e hH hc he hs).art u) =
      thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) :=
  congrArg (thetaA Ξ e χ hχ) ((mul_assoc _ _ _).trans
    ((congrArg (_ * ·) ((data Ξ e).w_mul_self ((data Ξ e).art hH u).1.1)).trans (mul_one _)))

theorem prim_theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) :
    PChar.of χ = (host Ξ e hH hc he hs).prim (theta Ξ e χ hχ) := by
  set H := host Ξ e hH hc he hs with hHdef
  refine An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M))
    ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩
  have haN : a.Coprime H.condN := ha.coprime_mul_right_right
  have haM : a.Coprime M := ha.coprime_mul_left_right
  have haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
    (Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)
  refine ((H.isPrimOf_prim _).2 a haN).trans ?_
  show _ = χ (a : ZMod M)
  rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]
  refine congrArg Units.val ?_
  have h1 := thetaA_toA Ξ e χ hχ (ZMod.unitOfCoprime a haW)
  rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at h1
  exact (theta_art Ξ e hH hc he hs χ hχ _).trans ((congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v))
    (unitsMap_unitOfCoprime ((data Ξ e).m_dvd q d) a haN)).trans h1)

theorem keptInXp : (host Ξ e hH hc he hs).KeptInXp (Level.ofSub Ξ).KEPT := fun ψ hψ => by
  obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ
  exact ⟨_, theta_mem Ξ e χ hχ, (HostRaw.isPrimOf_iff _ _ _).mpr (prim_theta Ξ e hH hc he hs χ hχ)⟩

theorem exceptional_character_condition : (host Ξ e hH hc he hs).ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK := by
  refine ⟨fun ψ h => (by cases h), fun _ h => ?_⟩
  obtain ⟨χ, hχ, h1⟩ := (Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)
  rw [prim_theta Ξ e hH hc he hs χ hχ] at h1
  have : NeZero (QS Ξ e * q * d) := (data Ξ e).neZeroN hH
  have : NeZero ((data Ξ e).m * q * d) := this
  have hco := coprime_QS Ξ e hH hc
  obtain ⟨y, cy, hy⟩ := D7.exists_sign hH.1 (D7.q4 hH) (-1)
  obtain ⟨u, u1, u2, -⟩ := exists_unit_three hco.coprime_mul_right_right hco.coprime_mul_left_right (D7.cop_qd hH)
    1 y 1 (Nat.coprime_one_left _) cy (Nat.coprime_one_left _)
  have h2 := (theta_art Ξ e hH hc he hs χ hχ u).symm.trans (HostRaw.art_eq_of_prim_eq _ h1 u)
  have h3 : thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) = 1 :=
    (congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v))
      ((unitsMap_eq_one_iff ((data Ξ e).m_dvd q d) u).mpr u1)).trans
      ((congrArg (thetaA Ξ e χ hχ) (map_one (data Ξ e).toA)).trans (map_one _))
  have h4 : ((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) = -1 := ((data Ξ e).art_ps hH u).trans ((D7.jac_congr u2).trans hy)
  have h5 : (1 : ℂ) = (((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) : ℂ) := congrArg Units.val (h3.symm.trans h2)
  rw [h4] at h5
  norm_num at h5


end Host

end AnyGrp

end Formalism.HC

end
