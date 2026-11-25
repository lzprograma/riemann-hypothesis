module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Mum

alias degPre_c_zero := _root_.GlobalTheory.IndivisibleSection.c_zero_eq_one

theorem tens_inc_pr_facts (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r) :
    IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧
      ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).one_hom]
    split_ifs
    · simp
    · rw [comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, T.inc_pr']
    split_ifs
    · simp
    · rw [comp_one]
      have : ((1 : D.P.A ⟶ D.P.A) ⊗ₘ (1 : D.P.A ⟶ D.P.A)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1) := by
        ext <;> simp
      rw [this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]
  · simpa using T.inc_pr' i₀ i₀
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', Tens.act_pr]
    by_cases h : i = i₀
    · subst h
      rw [ite_eq_left rfl, Category.comp_id, Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    · rw [ite_eq_right h, comp_one]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp [Ne.symm h]
  · intro y
    apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', T.c_pr]
    by_cases h : i = i₀
    · subst h
      simp [Tens.xi]
    · rw [ite_eq_right h, comp_one]
      simp [Tens.xi, h, degPre_c_zero]

end GlobalTheory.Mum
