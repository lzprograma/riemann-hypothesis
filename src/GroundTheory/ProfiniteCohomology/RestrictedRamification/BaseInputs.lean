module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteRoots
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnits
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem finite_of_exact_of_finite {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Finite A]
    [Finite C] (g : A →+ B) (f : B →+ C) (hex : ∀ b, f b = 0 → ∃ a, g a = b) : Finite B := by
  rw [f.finite_iff_finite_ker_range]
  refine ⟨?_, inferInstance⟩
  have hsub : (f.ker : Set B) ⊆ Set.range g := fun b hb => hex b hb
  exact ((Set.finite_range g).subset hsub).to_subtype

theorem exists_natCast_mem_place (K : FiniteSubfield) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal :=
  by apply _root_.GroundTheory.ProfCoh.exists_place_above; assumption

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (n ℓ k : ℕ) (hℓ : ℓ.Prime)
  (hnk : n = ℓ ^ k) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)


include hℓ hS in
theorem nonempty_of_natCast_mem : Nonempty S :=
  (exists_natCast_mem_place K hℓ).elim fun v hv => ⟨⟨v, hS v hv⟩⟩


include hnk hS in
theorem mem_of_natCast_pow_mem : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  subst hnk
  rw [Nat.cast_pow] at hv
  exact hS v (v.isPrime.mem_of_pow_mem k hv)

variable [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1)


include hnk hS hodd in
theorem subsingleton_gsRoots_three : Subsingleton (cohomology (gsRoots S n) 3) :=
  subsingleton_cohomology_of_cdp_le_two (NeZero.ne n)
    (fun _ hp hpn => cdp_galUnramifiedOutside_le_two_of_dvd K S (NeZero.ne n)
      (mem_of_natCast_pow_mem S n ℓ k hnk hS) hodd hp hpn) (gsRoots S n) (nsmul_gsRoots S n) le_rfl


include hnk hS hodd in
theorem subsingleton_zmodRep_gs_three :
    Subsingleton (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 3) :=
  subsingleton_cohomology_of_cdp_le_two (NeZero.ne n)
    (fun _ hp hpn => cdp_galUnramifiedOutside_le_two_of_dvd K S (NeZero.ne n)
      (mem_of_natCast_pow_mem S n ℓ k hnk hS) hodd hp hpn) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
    (nsmul_zmodRep_eq_zero _ n) le_rfl

omit [NeZero n] in
theorem natCard_zmodRep (G : Type) [Group G] : Nat.card (zmodRep.{0} G n) = n := by
  change Nat.card (ULift.{0} (ZMod n)) = n
  rw [Nat.card_ulift, Nat.card_zmod]

variable [Finite S]


include hnk hS in
theorem finite_zmodRep_gs_one : Finite (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) := by
  have : Finite (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) := inferInstanceAs (Finite (ULift.{0} (ZMod n)))
  refine finite_cohomology_gs K S _ (fun v hv => ?_) 1 (by norm_num)
  rw [natCard_zmodRep] at hv
  exact mem_of_natCast_pow_mem S n ℓ k hnk hS v hv

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))


omit [Finite S] in
include hnk hS in
theorem natCard_gsRoots : Nat.card (gsRoots S n) = n := by
  change Nat.card (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) = n
  rw [Nat.card_congr Additive.toMul]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ n
  have hmem : ζ ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S (NeZero.ne n)
      (fun v hv h => hv (mem_of_natCast_pow_mem S n ℓ k hnk hS v h)) hζ.pow_eq_one
  have hζS : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) hζ
      Subtype.val_injective
  exact hζS.card_rootsOfUnity


omit [Finite S] in
include hnk hS in
theorem finite_gsRoots_local_one (v : S) :
    Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1) := by
  have : Finite (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))))
  refine finite_cohomology_localField _ ?_ 1
  change ((Nat.card (gsRoots S n) : ℕ) : (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≠ 0
  rw [natCard_gsRoots S n ℓ k hnk hS]
  exact Nat.cast_ne_zero.2 (NeZero.ne n)


include hnk hS in
theorem finite_gsRoots_compact_two [Fintype S] :
    Finite (compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2) := by
  have : ∀ v : S, Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1) :=
    finite_gsRoots_local_one S n ℓ k hnk hS ιs
  have hA : Finite (ModuleCat.of (ULift.{0} ℤ)
      (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1)) :=
    inferInstanceAs (Finite (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1))
  have hC : Finite (cohomology (gsRoots S n) 2) :=
    finite_cohomology_rootsOfUnity K S n (NeZero.ne n) (mem_of_natCast_pow_mem S n ℓ k hnk hS) 2 le_rfl
  exact finite_of_exact_of_finite
    (localToCompact (gsFinFamily S ιs) (gsRoots S n) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (fun _ => 𝟙 _) 1).hom.toAddMonoidHom
    (compactToGlobal (gsFinFamily S ιs) (gsRoots S n) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (fun _ => 𝟙 _) 2).hom.toAddMonoidHom
    (fun b hb => (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
      (compactCohomology_exact_compact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 1) hb)

end

section PlacesOver

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))

@[instance_reducible]
noncomputable def fintypePlacesOver [Finite S] : Fintype (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  (placesOver_finite (Set.toFinite S)).fintype

theorem nonempty_placesOver_of_natCast_mem {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  nonempty_of_natCast_mem (placesOver S) ℓ hℓ fun _ hw => mem_placesOver_of_natCast_mem hS hw

end PlacesOver

end GroundTheory.ProfCoh
