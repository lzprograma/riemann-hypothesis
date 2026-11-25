module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndExt

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

abbrev red (n r : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ r))


variable (k) in
def H (n r : ℕ) : Subgroup (GL (Fin n) k) := (red (k := k) n r).ker.map (incl n)

theorem inPow_algebraMap (r : ℕ) (y : 𝒪[k]) :
    InPow r (algebraMap 𝒪[k] k y) ↔ y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  constructor
  · rintro ⟨z, hz, e⟩
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  · intro h
    exact ⟨y, h, rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_sub (n : ℕ) (u : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (((incl n u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) =
      algebraMap 𝒪[k] k ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) := by
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map]

theorem red_eq_one_iff (n r : ℕ) (u : GL (Fin n) 𝒪[k]) :
    red (k := k) n r u = 1 ↔ ∀ i j, ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) ∈
      IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  rw [Units.ext_iff]
  constructor
  · intro h i j
    have h' := congrFun (congrFun h i) j
    rw [← Ideal.Quotient.eq]
    split_ifs with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
  · intro h
    ext i j
    have h' := Ideal.Quotient.eq.2 (h i j)
    split_ifs at h' with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'

theorem mem_KC_iff (n r : ℕ) (g : GL (Fin n) k) : g ∈ KC k n r ↔ g ∈ H k n r := by
  constructor
  · rintro ⟨⟨u, rfl⟩, hP⟩
    refine ⟨u, (red_eq_one_iff n r u).2 fun i j => ?_, rfl⟩
    have := hP i j
    rwa [entry_sub, inPow_algebraMap] at this
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [entry_sub, inPow_algebraMap]
    exact (red_eq_one_iff n r u).1 hu i j

theorem coe_H (n r : ℕ) : (H k n r : Set (GL (Fin n) k)) = KC k n r :=
  Set.ext fun g => (mem_KC_iff n r g).symm

end UpperTheory.TNZ.Grp.P_KC

namespace UpperTheory.TNZ.Grp

open P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_KC {n : ℕ} (G : Grp k n) : CompactOpenKernelProp G := by
  intro hB r
  refine ⟨?_, ?_, P_indExt.isOpen_KC n r, fun g hg => hg.1, ?_⟩
  · show ((Subgroup.closure (KC k n r) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = KC k n r
    rw [← coe_H, Subgroup.closure_eq]
  · intro g hg u hu
    obtain ⟨v, rfl⟩ := hg
    obtain ⟨w, hw, rfl⟩ := (mem_KC_iff n r u).1 hu
    refine (mem_KC_iff n r _).2 ⟨v * w * v⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hw ⊢
    simp [hw]
  · intro hr g hg
    refine ⟨hg.1, fun i j hij => ?_⟩
    have hne : i ≠ j := fun h => (ne_of_lt hij) (h ▸ rfl)
    obtain ⟨y, hy, e⟩ := hg.2 i j
    rw [ite_eq_right hne, sub_zero] at e
    have hc : cc G.μ (G.bl j) (G.bl i) ≤ r := (hB.2.1 (G.bl j) (G.bl i)).le.trans hr
    exact ⟨y, Ideal.pow_le_pow_right hc hy, e⟩

end UpperTheory.TNZ.Grp
