module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.QdetFacts

@[expose] public section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem lift_apply (B : Module.End ℂ M) (f : TV n M P) (I : P → Fin n) : lift B f I = B (f I) := rfl

omit [Fintype P] in
theorem eAt_apply (p : P) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    eAt p a b f I = if I p = a then f (Function.update I p b) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> simp

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_apply (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) : pm σ f I = f (I ∘ σ) := rfl

omit [Fintype P] in
theorem tE_apply (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    tE S E a b f I = E a b (f I) + ∑ p ∈ S, if I p = a then f (Function.update I p b) else 0 := by
  simp only [tE, LinearMap.add_apply, Pi.add_apply, lift_apply, LinearMap.sum_apply, Finset.sum_apply, eAt_apply]

omit [Fintype P] in
theorem Om_apply (E : Fin n → Fin n → Module.End ℂ M) (p : P) (f : TV n M P) (I : P → Fin n) :
    Om E p f I = ∑ a, E a (I p) (f (Function.update I p a)) := by
  simp only [Om, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply, eAt_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I p)]
  · simp
  · intro b _ hb
    rw [ite_eq_right (Ne.symm hb), map_zero]
  · simp

omit [Fintype P] [DecidableEq P] in
theorem pm_mul (σ τ : Equiv.Perm P) : (pm (σ * τ) : Module.End ℂ (TV n M P)) = pm σ * pm τ := rfl

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_one : (pm 1 : Module.End ℂ (TV n M P)) = 1 := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_mul (B B' : Module.End ℂ M) : (lift (B * B') : Module.End ℂ (TV n M P)) = lift B * lift B' := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_comm_pm (B : Module.End ℂ M) (σ : Equiv.Perm P) : Commute (lift B : Module.End ℂ (TV n M P)) (pm σ) := rfl

def liftA (n : ℕ) (M P : Type) [AddCommGroup M] [Module ℂ M] : Module.End ℂ M →ₐ[ℂ] Module.End ℂ (TV n M P) where
  toFun := lift
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype P] in
theorem lift_comm_eAt (B : Module.End ℂ M) (p : P) (a b : Fin n) : Commute (lift B) (eAt p a b) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, eAt_apply]
  split_ifs <;> simp

theorem alt_apply (G : Finset (Equiv.Perm P)) (f : TV n M P) (I : P → Fin n) :
    alt G f I = ∑ σ ∈ G, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ σ) := by
  simp only [alt, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, pm_apply]

theorem cA_apply {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA col b f = alt (colG col) f b := rfl

theorem actT_apply {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M P) (I : P → Fin n) :
    actT lab κ ρ γ f I = ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • ρ γ (f J) := by
  simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem curF_apply {m k : ℕ} (f : TV n M (Fin (m + k))) (J : Fin k → Fin n) (I : Fin m → Fin n) :
    curF n M m k f J I = f (Fin.append I J) := rfl

section SharedAlg

theorem liftA_apply {n : ℕ} {M P : Type} [AddCommGroup M] [Module ℂ M] (B : Module.End ℂ M) :
    liftA n M P B = lift B := rfl

theorem lift_alg {n : ℕ} {M P : Type} [AddCommGroup M] [Module ℂ M] (c : ℂ) :
    (lift (algebraMap ℂ (Module.End ℂ M) c) : Module.End ℂ (TV n M P)) = algebraMap ℂ _ c :=
  (liftA n M P).commutes c

theorem qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp [qdet, qminor, Tm, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite φ]

theorem glRel_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    {E : Fin m → Fin m → A} (h : GlRel E) : GlRel fun a b => φ (E a b) := by
  intro a b c d
  have := congrArg φ (h a b c d)
  simpa only [map_sub, map_mul, apply_ite φ, map_zero] using this

theorem qdet_commute {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ) (Z : A)
    (h : ∀ a b, Commute (E a b) Z) : Commute (qdet E u) Z := by
  unfold qdet qminor
  refine Commute.sum_left _ _ _ fun σ _ =>
    Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

theorem pm_single {n : ℕ} {M P : Type} [AddCommGroup M] [Module ℂ M] [Fintype P] [DecidableEq P]
    (σ : Equiv.Perm P) (I : P → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M P) = Pi.single (I ∘ σ.symm) v := by
  funext J
  rw [pm_apply]
  simp only [Pi.single_apply, Equiv.eq_comp_symm]

theorem eAt_comm {n : ℕ} {M P : Type} [AddCommGroup M] [Module ℂ M] [DecidableEq P]
    {p q : P} (h : p ≠ q) (a b c d : Fin n) :
    Commute (eAt p a b : Module.End ℂ (TV n M P)) (eAt q c d) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [mul_apply_eq_comp, eAt_apply, Function.update_of_ne h, Function.update_of_ne h.symm,
    Function.update_comm h b d I]
  split_ifs <;> rfl

end SharedAlg

end PositivityTheory.Rg.Cz

end
