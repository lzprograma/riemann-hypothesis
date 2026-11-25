module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees.Layers
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import GroundTheory.GlobalFields.CyclotomicCharacters.DegreeDecomposition

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract
  FiniteSubfield IsDedekindDomain

open scoped GroundTheory.LocalField.Abstract Pointwise GroundTheory.Global.SemiLocal

noncomputable section

namespace CyclotomicLayer

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem degreeMod_eq_one_of_mem_fixingSubgroup (q : Nat.Primes) (a : ℕ) {σ : Gal(ℚ̄/ℚ)}
    (hσ : σ ∈ (rootsOfUnityField ((q : ℕ) ^ (a + unitsLevel (q : ℕ)))).fixingSubgroup) :
    degreeMod (primePowPNat (q : ℕ) a) σ = 1 := by
  have hq : Fact (q : ℕ).Prime := ⟨q.2⟩
  have : NeZero ((q : ℕ) ^ (a + unitsLevel (q : ℕ))) := ⟨pow_ne_zero _ q.2.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ ((q : ℕ) ^ (a + unitsLevel (q : ℕ)))
  have hζmem : ζ ∈ rootsOfUnityField ((q : ℕ) ^ (a + unitsLevel (q : ℕ))) :=
    subset_adjoin ℚ _ hζ.pow_eq_one
  have h1 := modCharacter_eq_one hζ ((mem_fixingSubgroup_iff _ _).1 hσ ζ hζmem)
  have h2 : redUnits (q : ℕ) (a + unitsLevel (q : ℕ))
      (Units.map (toPadicInt (q : ℕ)).toMonoidHom (character σ)) = 1 := by
    apply Units.ext
    rw [redUnits_character, h1]
  apply Multiplicative.toAdd.injective
  rw [toAdd_degreeMod, toAdd_one, ← toZModPow_toPadicInt, toPadicInt_degree, degreeComponent_apply,
    toZModPow_padicUnitsLog, h2, map_one, toAdd_one]
  rfl

theorem zhatLayerField_le_rootsOfUnityField (q : Nat.Primes) (a : ℕ) :
    zhatLayerField (primePowPNat (q : ℕ) a) ≤ rootsOfUnityField ((q : ℕ) ^ (a + unitsLevel (q : ℕ))) := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  intro x hx
  rw [zhatLayerField, mem_fixedField_iff] at hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup (rootsOfUnityField _), mem_fixedField_iff]
  intro σ hσ
  exact hx σ (MonoidHom.mem_ker.2 (degreeMod_eq_one_of_mem_fixingSubgroup q a hσ))

end CyclotomicLayer

end

end GroundTheory.ProfCoh
