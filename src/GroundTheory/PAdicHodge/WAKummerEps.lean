module

public import GroundTheory.PAdicHodge.BStPeriod
public import GroundTheory.PAdicHodge.TateCpTwist
public import GroundTheory.PAdicHodge.BdRLattice
public import GroundTheory.PAdicHodge.BdRTGalois
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open Ideal WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

section Cp

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt 𝒪 p
local notation "𝕎𝒪♭" => WittVector p 𝒪♭
local notation "𝔹" => BDeRhamPlus 𝒪 p
local notation "𝔪" => maximalIdeal 𝔹
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv 𝒪♭ p)

local instance instNeZeroPowPrime (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩

theorem tilt_ext_untilt {x y : 𝒪♭}
    (h : ∀ n, PreTilt.untilt (φi^[n] x) = PreTilt.untilt (φi^[n] y)) : x = y :=
  IsPerfectoidField.preTilt_ext p fun n => by
    rw [← IsPerfectoidField.mk_untilt_iterate, h, IsPerfectoidField.mk_untilt_iterate]

theorem untilt_iterate_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) (n : ℕ) :
    PreTilt.untilt (φi^[n] (IsPerfectoidField.ofCompatible p y hy)) = y n := by
  have e : φi^[n] (IsPerfectoidField.ofCompatible p y hy) =
      IsPerfectoidField.ofCompatible p (fun m => y (m + n)) (fun m => by
        rw [show m + 1 + n = (m + n) + 1 by omega]; exact hy (m + n)) := by
    refine IsPerfectoidField.preTilt_ext p fun m => ?_
    rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, IsPerfectoidField.coeff_ofCompatible,
      IsPerfectoidField.coeff_ofCompatible]
  rw [e, IsPerfectoidField.untilt_ofCompatible, zero_add]


omit hp in
theorem pow_eq_pow_of_mod_eq {M : Type*} [Monoid M] {ζ : M} {N u v : ℕ} (hζ : ζ ^ N = 1)
    (h : u % N = v % N) : ζ ^ u = ζ ^ v := by
  rw [← Nat.mod_add_div u N, ← Nat.mod_add_div v N, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow,
    one_pow, h]

theorem val_toZModPow_mod (a : ℤ_[p]) {m n : ℕ} (h : m ≤ n) :
    (PadicInt.toZModPow n a).val % p ^ m = (PadicInt.toZModPow m a).val := by
  rw [← PadicInt.zmod_cast_comp_toZModPow m n h, RingHom.comp_apply, ZMod.castHom_apply,
    ZMod.cast_eq_val, ZMod.val_natCast]

theorem untilt_iterate_pow_eq_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    PreTilt.untilt (φi^[n] ε) ^ p ^ n = 1 := by
  rw [PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, hε]

def epsSeq (ε : 𝒪♭) (a : ℤ_[p]) (n : ℕ) : 𝒪 :=
  PreTilt.untilt (φi^[n] ε) ^ (PadicInt.toZModPow n a).val

theorem epsSeq_succ_pow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) (n : ℕ) :
    epsSeq ε a (n + 1) ^ p = epsSeq ε a n := by
  rw [epsSeq, epsSeq, ← pow_mul, mul_comm, pow_mul, IsPerfectoidField.untilt_iterate_succ_pow]
  exact pow_eq_pow_of_mod_eq (untilt_iterate_pow_eq_one hε n)
    ((val_toZModPow_mod a (Nat.le_succ n)).trans (Nat.mod_eq_of_lt (ZMod.val_lt _)).symm)

def epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) : 𝒪♭ :=
  IsPerfectoidField.ofCompatible p (epsSeq ε a) (epsSeq_succ_pow hε a)

theorem untilt_iterate_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) (n : ℕ) :
    PreTilt.untilt (φi^[n] (epsPow hε a)) =
      PreTilt.untilt (φi^[n] ε) ^ (PadicInt.toZModPow n a).val :=
  untilt_iterate_ofCompatible _ _ n

theorem isPrimitiveRoot_untilt_iterate {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt (φi ε) ≠ 1) (n : ℕ) :
    IsPrimitiveRoot (PreTilt.untilt (φi^[n] ε)) (p ^ n) := by
  rcases n with _ | m
  · rw [Function.iterate_zero, id, hε, pow_zero]
    exact IsPrimitiveRoot.one
  · have hord : orderOf (PreTilt.untilt (φi^[m + 1] ε)) = p ^ (m + 1) := by
      refine orderOf_eq_prime_pow ?_ (untilt_iterate_pow_eq_one hε (m + 1))
      rw [Function.iterate_succ_apply, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
      exact hζ
    rw [← hord]
    exact IsPrimitiveRoot.orderOf _

theorem exists_epsPow_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1) {η : 𝒪♭}
    (hη : PreTilt.untilt η = 1) : ∃ a : ℤ_[p], epsPow hε a = η := by
  have hex : ∀ n, ∃ i < p ^ n, PreTilt.untilt (φi^[n] ε) ^ i = PreTilt.untilt (φi^[n] η) :=
    fun n => (isPrimitiveRoot_untilt_iterate hε hζ n).eq_pow_of_pow_eq_one
      (untilt_iterate_pow_eq_one hη n)
  choose k hk hkη using hex
  have hi : ∀ n, (p : ℤ) ^ n ∣ (k (n + 1) : ℤ) - (k n : ℤ) := by
    intro n
    have e : PreTilt.untilt (φi^[n] ε) ^ (k (n + 1) % p ^ n) = PreTilt.untilt (φi^[n] ε) ^ k n := by
      rw [pow_eq_pow_of_mod_eq (untilt_iterate_pow_eq_one hε n) (Nat.mod_mod _ _), hkη n,
        ← IsPerfectoidField.untilt_iterate_succ_pow (x := ε), pow_right_comm, hkη (n + 1),
        IsPerfectoidField.untilt_iterate_succ_pow]
    have hm : k n % p ^ n = k (n + 1) % p ^ n := by
      rw [Nat.mod_eq_of_lt (hk n)]
      exact ((isPrimitiveRoot_untilt_iterate hε hζ n).pow_inj (Nat.mod_lt _ (NeZero.pos _)) (hk n) e).symm
    have := (Nat.modEq_iff_dvd.1 hm)
    exact_mod_cast this
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) p hi),
    tilt_ext_untilt fun n => ?_⟩
  rw [untilt_iterate_epsPow, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p hi, Int.cast_natCast,
    ZMod.val_cast_of_lt (hk n), hkη n]

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

abbrev tiltGal (σ : Gal(PadicAlgCl p/K)) : 𝒪♭ →+* 𝒪♭ :=
  preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)

theorem exists_tiltGal_eq_mul {x : 𝒪♭} (hx : x ≠ 0) {σ : Gal(PadicAlgCl p/K)}
    (hσ : σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p])) :
    ∃ η : 𝒪♭, PreTilt.untilt η = 1 ∧ tiltGal σ x = x * η := by
  have hcoe : ((PreTilt.untilt (tiltGal σ x) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]) := by
    rw [tiltGal, AInf.coe_untilt_gal, hσ]
  obtain ⟨η, hη⟩ : x ∣ tiltGal σ x :=
    preTilt_dvd_iff_norm_le.2 (le_of_eq (by rw [preTilt_norm_def, preTilt_norm_def, hcoe]))
  refine ⟨η, ?_, hη⟩
  have h := congrArg (fun y => ((PreTilt.untilt y : 𝒪) : ℂ_[p])) hη
  simp only [map_mul, MulMemClass.coe_mul] at h
  rw [hcoe] at h
  have hx0 : ((PreTilt.untilt x : 𝒪) : ℂ_[p]) ≠ 0 := by
    intro h0
    exact hx ((IsPerfectoidField.untilt_eq_zero_iff (p := p)).1 (Subtype.ext (by simpa using h0)))
  apply Subtype.ext
  rw [OneMemClass.coe_one]
  exact (mul_eq_left₀ hx0).1 h.symm

theorem pFlat_ne_zero : pFlat p ≠ 0 := fun h => by
  have h1 := coe_untilt_pFlat (p := p)
  rw [h, IsPerfectoidField.untilt_zero] at h1
  exact natCast_p_ne_zero_cp (p := p) (by simpa using h1.symm)

theorem gal_smul_coe_untilt_pFlat (σ : Gal(PadicAlgCl p/K)) :
    σ • ((PreTilt.untilt (pFlat p) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (pFlat p) : 𝒪) : ℂ_[p]) := by
  rw [coe_untilt_pFlat, ← galCp_apply, map_natCast]

end Cp

end GroundTheory.PAdicHodge
