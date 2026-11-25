module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothCone
import Mathlib.Tactic.Linter.Style

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.Cells

theorem finite_families : ∀ (F : Type) (S : Set F), S.Finite →
    {x : Σ m : ℕ, Fin m → F | (∀ j, x.2 j ∈ S) ∧ Function.Injective x.2}.Finite := by
  intro F S hS
  classical
  refine (Set.Finite.biUnion (Finset.range (hS.toFinset.card + 1)).finite_toSet fun m _ =>
    ((Set.Finite.pi (t := fun _ : Fin m => S) fun _ => hS).image (Sigma.mk m))).subset ?_
  rintro ⟨m, γ⟩ ⟨h1, h2⟩
  have hle : m ≤ hS.toFinset.card := by
    have := Fintype.card_le_of_injective (fun j : Fin m => (⟨γ j, by simpa using h1 j⟩ : hS.toFinset))
      fun a b h => h2 (congrArg Subtype.val h)
    simpa using this
  exact Set.mem_biUnion (x := m) (by simp; omega) ⟨γ, fun j _ => h1 j, rfl⟩

theorem linearMap_eq_of_eq_on_residues : ∀ (N : ℕ), 2 ≤ N → ∀ (r : ℕ) (e₁ e₂ : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (V : Set (Fin r → ℤ)),
    (∀ x : Fin r → ℤ, ∃ v ∈ V, ∀ i, ((v i : ℤ) : ZMod N) = (x i : ZMod N)) → (∀ v ∈ V, e₁ v = e₂ v) → e₁ = e₂ := by
  intro N hN r e₁ e₂ V hV he
  set δ := e₁ - e₂ with hδ
  have h1 : ∀ x, ∃ z, δ x = (N : ℤ) • δ z := by
    intro x
    obtain ⟨v, hv, hvx⟩ := hV x
    have : ∀ i, (N : ℤ) ∣ x i - v i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (hvx i)
    choose z hz using this
    refine ⟨z, ?_⟩
    have hx : x = v + (N : ℤ) • z := funext fun i => by simp [← hz i]
    rw [hx, map_add (f := _), map_smul]
    simp [δ, he v hv]
  have h2 : ∀ k : ℕ, ∀ x, ∃ w, δ x = ((N : ℤ) ^ k) • w := by
    intro k
    induction k with
    | zero => intro x; exact ⟨δ x, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨z, hz⟩ := h1 x
      obtain ⟨w, hw⟩ := ih z
      exact ⟨w, by rw [hz, hw, smul_smul, pow_succ']⟩
  have h3 : δ = 0 := by
    refine LinearMap.ext fun x => funext fun i => ?_
    obtain ⟨w, hw⟩ := h2 (δ x i).natAbs x
    generalize hk : (δ x i).natAbs = k at hw
    have hd : ((N : ℤ) ^ k) ∣ δ x i := ⟨w i, by simpa using congrFun hw i⟩
    by_contra h0
    have h4 := Int.natAbs_le_of_dvd_ne_zero hd h0
    have h5 : k < N ^ k := Nat.lt_pow_self (by omega)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h4
    omega
  exact sub_eq_zero.1 h3

theorem cong_map {N r : ℕ} (f : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) {x y : Fin r → ℤ}
    (h : ∀ i, ((x i : ℤ) : ZMod N) = (y i : ZMod N)) (i : Fin r) : ((f x i : ℤ) : ZMod N) = (f y i : ZMod N) := by
  have : ∀ i, (N : ℤ) ∣ y i - x i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i)
  choose z hz using this
  have hy : y = x + (N : ℤ) • z := funext fun i => by simp [← hz i]
  rw [hy, map_add (f := _), map_smul]
  simp

end GlobalTheory.Poinc.Cells
