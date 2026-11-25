module

public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PowDefs
import GroundTheory.ProfiniteCohomology.EulerChar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u w

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] {R : Type w} [CommMonoid R]


namespace IsMultiplicativeOn

variable {P : ℕ → Prop} {χ : (A : Rep.{u} k G) → [IsDiscreteRep A] → R}

theorem rangeStep (hχ : IsMultiplicativeOn P χ) (hPdvd : ∀ m n, m ∣ n → P n → P m)
    {A : Rep.{u} k G} [IsDiscreteRep A] [Finite A] (T : Module.End k A)
    (hT : ∀ g : G, Commute T (A.ρ g)) (D : Submodule k A) (hD : ∀ g : G, D ≤ D.comap (A.ρ g))
    (hA : P (Nat.card A)) :
    χ (Rep.subrepresentation A D hD) =
      χ (Rep.subrepresentation A _ (inf_ker_le_comap T hT D hD)) *
        χ (Rep.subrepresentation A _ (map_le_comap T hT D hD)) := by
  have hdvd : Nat.card D ∣ Nat.card A :=
    AddSubgroup.card_addSubgroup_dvd_card D.toAddSubgroup
  exact hχ.shortExact (S := rangeStepComplex T hT D hD)
    (rangeStepComplex_shortExact T hT D hD) (hPdvd _ _ hdvd hA)

variable [IsTopologicalGroup G] [CompactSpace G]

theorem coind_res_eq_pow (hχ : IsMultiplicativeOn P χ) (hPdvd : ∀ m n, m ∣ n → P n → P m)
    (hPmul : ∀ m n, P m → P n → P (m * n)) (H : OpenSubgroup G)
    [hN : (H : Subgroup G).Normal] [IsCyclic (G ⧸ (H : Subgroup G))] {p a : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card (G ⧸ (H : Subgroup G)) = p ^ a) (M : Rep.{u} k G) [IsDiscreteRep M]
    [Finite M] (hM : P (Nat.card M)) (hpM : ∀ m : M, p • m = 0) :
    χ (Rep.coind (H : Subgroup G).subtype (Rep.res (H : Subgroup G).subtype M)) =
      χ M ^ (p ^ a) :=
  coind_res_eq_pow_of_rangeStep χ (fun hA e => hχ.iso hA e)
    (fun T hT D hD hA => hχ.rangeStep hPdvd T hT D hD hA)
    hPdvd hPmul H hcard M hM hpM

end IsMultiplicativeOn

variable [IsTopologicalGroup G]

end GroundTheory.ProfCoh
