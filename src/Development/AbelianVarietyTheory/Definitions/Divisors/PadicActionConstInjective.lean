module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

@[expose] public section

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory

namespace GlobalTheory.PDivGroup.Test

open PDiv

variable {p : ℕ} {O : Type} [CommRing O]


open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory in
variable {p : ℕ} {O : Type} [CommRing O] in
theorem _root_.GlobalTheory.PDivGroup.Test.mulP_injective (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by
  intro x y hxy
  have hinj := _root_.GlobalTheory.CartierDual.map_injective_of_surjective (G.dual_mulP_surjective n)
  have hx := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) x
  have hy := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) y
  rw [hxy, ← hy] at hx
  exact (_root_.GlobalTheory.CartierDual.bidual O (G.A n)).injective (hinj hx)

theorem hodgeTate_values [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    (∀ t, hodgeTate (mu p O) t = 0) ∧ hodgeTate (const p O) (constGen p O) ≠ 0 := by
  refine ⟨fun t => Subsingleton.elim _ _, fun h => dlogT_ne_zero p O hp ?_⟩
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id,
    Category.id_comp] at h
  have h2 := LinearMap.congr_fun (omegaMap_comp (mu p O).bidual.hom (mu p O).bidual.inv) (dlogT p O)
  rw [Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h2
  rw [h2]
  exact (congrArg _ h).trans (map_zero _)

end GlobalTheory.PDivGroup.Test
