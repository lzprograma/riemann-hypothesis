module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem comm_of_mem_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {s : Set A} {X Z : A}
    (hX : X ∈ Algebra.adjoin ℂ s) (h : ∀ T ∈ s, Commute T Z) : Commute X Z := by
  have hs : s ⊆ Subalgebra.centralizer ℂ {Z} := fun T hT => by
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (h T hT).symm.eq
  have hX' := Algebra.adjoin_le hs hX
  rw [Subalgebra.mem_centralizer_iff] at hX'
  exact (hX' Z rfl).symm

variable {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
theorem qdet_lift (F : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (h : HasChar F l) :
    HasChar (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) l := by
  intro u
  have e : (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) = fun a b => liftA n M P (F a b) := by
    funext a b
    rw [liftA_apply]
  rw [e, ← qdet_map, h u, AlgHom.commutes]

omit [Fintype P] in
theorem tE_empty (F : Fin n → Fin n → Module.End ℂ M) :
    (tE (∅ : Finset P) F : Fin n → Fin n → Module.End ℂ (TV n M P)) = fun a b => lift (F a b) := by
  funext a b
  simp [tE]

omit [Fintype P] in
theorem tE_comm_lift (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (B : Module.End ℂ M)
    (h : ∀ c d, Commute (F c d) B) (a b : Fin n) :
    Commute (tE S F a b : Module.End ℂ (TV n M P)) (lift B) := by
  unfold tE
  refine Commute.add_left ?_ (Commute.sum_left _ _ _ fun p _ => ?_)
  · have hc := (h a b).map (liftA n M P)
    simpa only [liftA_apply] using hc
  · unfold Commute SemiconjBy
    refine LinearMap.ext fun x => funext fun I => ?_
    simp only [Module.End.mul_apply, eAt, lift, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    split_ifs <;> simp

theorem cA_lift {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (B : Module.End ℂ M) :
    cA col b ∘ₗ lift B = B ∘ₗ (cA col b : TV n M P →ₗ[ℂ] M) := by
  refine LinearMap.ext fun x => ?_

  simp [cA, alt, pm, lift, map_sum]

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ W →ₐ[ℂ] Module.End ℂ V where
  toFun X := e.symm.toLinearMap ∘ₗ X ∘ₗ e.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' X Y := LinearMap.ext fun v => by simp
  map_zero' := LinearMap.ext fun v => by simp
  map_add' X Y := LinearMap.ext fun v => by simp
  commutes' r := LinearMap.ext fun v => by simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (X : Module.End ℂ W) (v : V) : cj e X v = e.symm (X (e v)) := rfl

end PositivityTheory.Rg.Cz.TA

end
