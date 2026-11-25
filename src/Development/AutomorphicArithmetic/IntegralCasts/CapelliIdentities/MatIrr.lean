module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Qf5.MatIrr.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] → {R : Type u_2} → [CommRing R] → {m : ℕ} → Subgroup G → (G → Matrix (Fin m) (Fin m) R) → Prop :=
    fun {G : Type u_1} [Group G] {R : Type u_2} [CommRing R] {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) ↦
      ∀ (W : Submodule R (Fin m → R)), (∀ g ∈ H, ∀ v ∈ W, (a g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.Qf5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R}
      (h : GL (Fin m) R),
      (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
        UpperTheory.Reformulated.B.Qf5.MatIrr U a → UpperTheory.Reformulated.B.Qf5.MatIrr U a' := by
  intro G R _ _ m U a a' h hconj hirr W hW
  let e := (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have hinv : ∀ g ∈ U, ∀ v ∈ W.comap e.toLinearMap,
      (a g).mulVec v ∈ W.comap e.toLinearMap := by
    intro g hg v hv
    change (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W at hv
    change (↑h : Matrix (Fin m) (Fin m) R).mulVec ((a g).mulVec v) ∈ W
    rw [hconj g hg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul, ← Matrix.mulVec_mulVec]
    exact hW g hg _ hv
  have cancel := Submodule.comap_injective_of_surjective e.surjective
  rcases hirr _ hinv with hb | ht
  · have hbot : (⊥ : Submodule R (Fin m → R)).comap e.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr e.injective
    exact Or.inl (cancel (hb.trans hbot.symm))
  · exact Or.inr (cancel (ht.trans (Submodule.comap_top _).symm))
