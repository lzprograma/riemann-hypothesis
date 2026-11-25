module

public import Mathlib.RingTheory.Length
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace Formalism.L2.NCov

open Module

section

variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem length_eq_of_bijective (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Bijective f) :
    Module.length R' M' = Module.length R M := by
  letI := RingHomInvPair.of_ringEquiv φ
  letI := RingHomInvPair.symm (φ : R →+* R') (φ.symm : R' →+* R)
  let e : M ≃ₛₗ[(φ : R →+* R')] M' := LinearEquiv.ofBijective f hf
  rw [Module.length_eq_height, Module.length_eq_height,
    ← Order.height_orderIso (Submodule.orderIsoMapComap e) ⊤, OrderIso.map_top]

private theorem length_quotient_eq_of_bijective_semilinear (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M')
    (hf : Function.Bijective f) (q : Submodule R M) (q' : Submodule R' M')
    (h : ∀ x, f x ∈ q' ↔ x ∈ q) :
    Module.length R' (M' ⧸ q') = Module.length R (M ⧸ q) := by
  let g : (M ⧸ q) →ₛₗ[(φ : R →+* R')] (M' ⧸ q') := q.mapQ q' f (fun x hx => (h x).2 hx)
  refine length_eq_of_bijective φ g ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective q y
    have hy' : (Submodule.Quotient.mk (f a) : M' ⧸ q') = 0 := hy
    rw [Submodule.Quotient.mk_eq_zero] at hy'
    rw [Submodule.Quotient.mk_eq_zero]
    exact (h a).1 hy'
  · intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective q' y
    obtain ⟨a, rfl⟩ := hf.2 b
    exact ⟨Submodule.Quotient.mk a, rfl⟩

theorem length_quot_map (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Injective f)
    (p q : Submodule R M) :
    haveI := RingHomInvPair.of_ringEquiv φ
    Module.length R' (↥(p.map f) ⧸ (q.map f).comap (p.map f).subtype) =
      Module.length R (↥p ⧸ q.comap p.subtype) := by
  let _ := RingHomInvPair.of_ringEquiv φ
  let _ := RingHomInvPair.symm (φ : R →+* R') (φ.symm : R' →+* R)
  let g := Submodule.equivMapOfInjective f hf p
  refine length_quotient_eq_of_bijective_semilinear φ g.toLinearMap g.bijective _ _ fun x => ?_
  change (x : M) ∈ (q.map f).comap f ↔ (x : M) ∈ q
  rw [Submodule.comap_map_eq_of_injective hf]

theorem length_quot_natCast (φ : R ≃+* R') (n : ℕ) :
    Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length R (R ⧸ Ideal.span {(n : R)}) := by
  let F : R →ₛₗ[(φ : R →+* R')] R' :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r x => by simp only [smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] }
  refine length_quotient_eq_of_bijective_semilinear φ F φ.bijective _ _ ?_
  intro x
  show φ x ∈ Ideal.span {(n : R')} ↔ x ∈ Ideal.span {(n : R)}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨φ.symm c, by apply φ.injective; simp [hc]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨φ c, by simp⟩

end

end Formalism.L2.NCov
