module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace GlobalTheory.AddEquivOfSurjectiveKernel

universe u_1 u_2 u_3

theorem exists_addEquiv_of_surjective_of_ker_iff {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : A →+ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a : A, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a : A, e (f a) = g a := by
  have hker : f.ker = g.ker := AddSubgroup.ext h
  let e := QuotientAddGroup.liftEquiv f.ker hf rfl
  refine ⟨e.symm.trans (QuotientAddGroup.liftEquiv f.ker hg hker), fun a => ?_⟩
  exact congrArg (QuotientAddGroup.liftEquiv f.ker hg hker)
    (e.symm_apply_apply (QuotientAddGroup.mk a))

end GlobalTheory.AddEquivOfSurjectiveKernel
