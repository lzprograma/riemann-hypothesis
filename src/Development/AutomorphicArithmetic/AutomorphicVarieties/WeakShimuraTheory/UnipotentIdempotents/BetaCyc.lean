module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
open scoped Pointwise

theorem UpperTheory.V.Ws.Lk.betaCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ Ω) [NumberField K], Module.finrank ℚ K = 2 → ∀ A₀ : ValuationSubring Ω, A₀.valuation (l : Ω) < 1 → ∀ β : G K Ω →* (PadicAlgCl l)ˣ, (∀ σ ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = σ * resQ K s * σ⁻¹ → β s * β s' = 1) → ∀ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) → (∀ B : ValuationSubring Ω, (∀ x ∈ K, x ∈ B ↔ x ∈ A₀) → ∀ s ∈ U ⊓ Ine (F := K) B, (β s : PadicAlgCl l) ^ 2 = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l s : ℤ_[l])) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ s ∈ Ine (F := K) A, (β s ^ 2 * cycBar K Ω l s ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ K _ hK A₀ hA₀ β hconj U hU hcyc A hA
  have hn : U.index ≠ 0 := by
    haveI : Finite (G K Ω ⧸ U) := U.quotient_finite_of_isOpen hU
    exact Subgroup.index_ne_zero_of_finite
  have hpow : ∀ s : G K Ω, s ^ U.index.factorial ∈ U := fun s =>
    Subgroup.pow_mem_of_index_ne_zero_of_dvd hn s (fun m h1 h2 => Nat.dvd_factorial h1 h2)
  have hkpos : 0 < U.index.factorial := Nat.factorial_pos _
  have hval : ∀ t : G K Ω, ((cycBar K Ω l t : (Qbar l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l t : ℤ_[l]) := fun t => rfl
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver
    (_root_.Formalism.BasicNotions.Examples₂.LB.isPlaceOver_vQ A₀ hA₀)
    (_root_.Formalism.BasicNotions.Examples₂.LB.isPlaceOver_vQ A hA)
  by_cases hσK : σ ∈ K.fixingSubgroup
  · refine ⟨1, U.index.factorial, hkpos, odd_one, ?_⟩
    have hB : ∀ x ∈ K, x ∈ A ↔ x ∈ A₀ := by
      intro x hx
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hfix : σ⁻¹ • x = x := (K.fixingSubgroup.inv_mem hσK) ⟨x, hx⟩
      rw [hfix]
    intro s hs
    have ht : s ^ U.index.factorial ∈ U ⊓ Ine (F := K) A := ⟨hpow s, pow_mem hs _⟩
    have h1 : β (s ^ U.index.factorial) ^ 2 = cycBar K Ω l (s ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A hB _ ht, hval])
    have e1 : (β s ^ 2 * cycBar K Ω l s ^ (-1 : ℤ)) ^ U.index.factorial =
        β (s ^ U.index.factorial) ^ 2 * (cycBar K Ω l (s ^ U.index.factorial))⁻¹ := by
      rw [map_pow, map_pow, zpow_neg, zpow_one]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e1, h1, mul_inv_cancel]
  · refine ⟨-1, U.index.factorial, hkpos, ⟨-1, by norm_num⟩, ?_⟩
    haveI hN : K.fixingSubgroup.Normal := by
      refine (InfiniteGalois.normal_iff_isGalois K).2 ?_
      haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
      exact isGalois_iff.2 ⟨Algebra.IsSeparable.of_integral _ _, Algebra.IsQuadraticExtension.normal ℚ K⟩
    intro s hs
    have hg : resQ K s ∈ Ine (F := ℚ) A := (resQ_Ine K A s).1 hs
    have hlift : IsLift (RingEquiv.refl ℚ) (σ : Ω ≃+* Ω) := fun y => by simp
    have hg' : conjGal hlift (resQ K s) ∈ Ine (F := ℚ) A₀ := by
      refine conjGal_mem_Ine hlift (fun x => ?_) hg
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      show σ⁻¹ • σ • x ∈ A₀ ↔ x ∈ A₀
      rw [inv_smul_smul]
    have heq : conjGal hlift (resQ K s) = σ⁻¹ * resQ K s * σ := by
      ext x
      rfl
    have hmem : σ⁻¹ * resQ K s * σ ∈ K.fixingSubgroup := by
      have h' := hN.conj_mem _ (resQ_mem K s) σ⁻¹
      rwa [inv_inv] at h'
    obtain ⟨s', hs'⟩ := exists_resQ hmem
    have hs'I : s' ∈ Ine (F := K) A₀ := (resQ_Ine K A₀ s').2 (by rw [hs', ← heq]; exact hg')
    have hσ' : σ⁻¹ ∉ K.fixingSubgroup := fun h' => hσK (by simpa using K.fixingSubgroup.inv_mem h')
    have hbb : β s * β s' = 1 := hconj σ⁻¹ hσ' s s' (by rw [hs', inv_inv])
    have hcy : cycBar K Ω l s' = cycBar K Ω l s := by
      show Units.map _ (cycZ K Ω l s') = Units.map _ (cycZ K Ω l s)
      have hz : cycZ ℚ Ω l (σ⁻¹ * resQ K s * σ) = cycZ ℚ Ω l (resQ K s) := by
        rw [map_mul, map_mul, map_inv, mul_comm (cycZ ℚ Ω l σ)⁻¹, inv_mul_cancel_right]
      rw [← resQ_cyc, ← resQ_cyc, hs', hz]
    have ht' : s' ^ U.index.factorial ∈ U ⊓ Ine (F := K) A₀ := ⟨hpow s', pow_mem hs'I _⟩
    have h1 : β (s' ^ U.index.factorial) ^ 2 = cycBar K Ω l (s' ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A₀ (fun _ _ => Iff.rfl) _ ht', hval])
    have hbs : β s = (β s')⁻¹ := eq_inv_of_mul_eq_one_left hbb
    have e2 : (β s ^ 2 * cycBar K Ω l s ^ (-(-1) : ℤ)) ^ U.index.factorial =
        (β (s' ^ U.index.factorial) ^ 2)⁻¹ * cycBar K Ω l (s' ^ U.index.factorial) := by
      rw [neg_neg, zpow_one, hbs, ← hcy, map_pow, map_pow]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e2, h1, inv_mul_cancel]
