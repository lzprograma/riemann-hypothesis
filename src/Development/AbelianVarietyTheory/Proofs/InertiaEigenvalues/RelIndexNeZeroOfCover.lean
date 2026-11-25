module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.ClassPet

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cong_mul {N : ℕ} {a b : GAf L n} (ha : NG.Cong L n N a) (hb : NG.Cong L n N b) :
    NG.Cong L n N (a * b) := by
  apply GlobalTheory.IsotOrth.cong_mul <;> assumption

theorem cong_one (N : ℕ) : NG.Cong L n N (1 : GAf L n) := by
  refine ⟨Subgroup.one_mem _, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩
  simp

theorem cong_inv {N : ℕ} {a : GAf L n} (ha : NG.Cong L n N a) : NG.Cong L n N a⁻¹ := by
  apply GlobalTheory.IsotOrth.cong_inv <;> assumption


variable (L n) in
def congSub (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | NG.Cong L n N κ}
  mul_mem' := cong_mul
  one_mem' := cong_one N
  inv_mem' := cong_inv

theorem congSub_le_umax (N : ℕ) : congSub L n N ≤ Umax L n := fun _ h => h.1

theorem congSub_mul_le (N M : ℕ) : congSub L n (N * M) ≤ congSub L n N := fun _ h => NG.Cong.of_mul_left L n h

end GlobalTheory.ClassPet

namespace GlobalTheory.ClassPet

section Grp
variable {G : Type*} [Group G]

theorem relIndex_ne_zero_of_cover {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H)
    (hle : H ≤ K) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    let φ : F → K ⧸ H.subgroupOf K := fun f =>
      if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)
    refine Finite.of_surjective φ (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H κ =>
      obtain ⟨f, hf, hfκ⟩ := hF κ κ.2
      have hfK : f ∈ K := by
        have := K.mul_mem κ.2 (K.inv_mem (hle hfκ))
        simpa using this
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [φ, dite_eq_left hfK]
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem exists_cosetReps {H K : Subgroup G} (hle : H ≤ K) (hne : H.relIndex K ≠ 0) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ K) ∧ (∀ κ ∈ K, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H) ∧ F.card = H.relIndex K := by
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let o : K ⧸ H.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have ho : Function.Injective o := by
    intro q q' h
    have : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (Quotient.out q).2
  · intro κ hκ
    refine ⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))
      simpa [Subgroup.mem_subgroupOf, o] using h
    · rintro u ⟨hu, hu'⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have : q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K) := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')
      rw [this]
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ]
    show _ = (H.subgroupOf K).index
    rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem norm_eq_one_of_relIndex {J K : Subgroup G} (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (χ : J →* ℂˣ)
    (hχ : ∀ κ (h : κ ∈ K), χ ⟨κ, hle h⟩ = 1) (κ : J) : ‖((χ κ : ℂˣ) : ℂ)‖ = 1 := by
  haveI : (K.subgroupOf J).FiniteIndex := ⟨hne⟩
  obtain ⟨i, j, hij, e⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => ((κ ^ i : J) : J ⧸ K.subgroupOf J))
  have hmem : ((κ ^ i)⁻¹ * κ ^ j : J) ∈ K.subgroupOf J := QuotientGroup.eq.1 e
  have h1 : χ ((κ ^ i)⁻¹ * κ ^ j) = 1 := by
    have := hχ _ (Subgroup.mem_subgroupOf.1 hmem)
    rwa [Subtype.coe_eta] at this
  have h2 : ((χ κ : ℂˣ) : ℂ) ^ i = ((χ κ : ℂˣ) : ℂ) ^ j := by
    rw [map_mul, map_inv, map_pow, map_pow, inv_mul_eq_one] at h1
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h1
    simpa using this
  have h3 : ‖((χ κ : ℂˣ) : ℂ)‖ ^ i = ‖((χ κ : ℂˣ) : ℂ)‖ ^ j := by rw [← norm_pow, ← norm_pow, h2]
  have hpos : 0 < ‖((χ κ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  by_contra hne1
  exact hij (pow_right_injective₀ hpos hne1 h3)

end Grp

section Sum
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
  (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))

theorem classSum_add_left (f₁ f₂ f' : GAf L n → a.W) :
    classSum a β J T (f₁ + f₂) f' = classSum a β J T f₁ f' + classSum a β J T f₂ f' := by
  simp only [classSum, Pi.add_apply, LinearMap.map_add₂, mul_add, Finset.sum_add_distrib]

theorem classSum_smul_left (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T (c • f) f' = starRingEnd ℂ c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_add_right (f f₁ f₂ : GAf L n → a.W) :
    classSum a β J T f (f₁ + f₂) = classSum a β J T f f₁ + classSum a β J T f f₂ := by
  simp only [classSum, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem classSum_smul_right (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T f (c • f') = c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_conj (hβ : IsInvForm a β) (f f' : GAf L n → a.W) :
    classSum a β J T f' f = starRingEnd ℂ (classSum a β J T f f') := by

  simp only [classSum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hβ.1 (f' t) (f t)]

end Sum

end GlobalTheory.ClassPet
