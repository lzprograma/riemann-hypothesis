module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

theorem UpperTheory.Reformulated.B.MultisetSeparation.msetSep :
    ∀ (m m' : Multiset ℂ),
    (∀ (u : ℂ), (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod) → m = m' := by
  intro m m' h
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod := by
    apply Polynomial.funext
    intro u
    simpa only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add] using h u
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr
