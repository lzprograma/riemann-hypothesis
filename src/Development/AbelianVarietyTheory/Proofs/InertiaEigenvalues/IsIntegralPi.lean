module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic

@[expose] public section

namespace GlobalTheory.IntegralPi

open Polynomial

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i)
    (hx : ∀ i, IsIntegral O (x i)) : IsIntegral O x := by
  classical
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ => hpm i), ?_⟩
  rw [← aeval_def]
  funext j
  have key : (aeval x (∏ i, p i)) j = aeval (x j) (∏ i, p i) := by
    have := (aeval_algHom_apply (Pi.evalAlgHom O R j) x (∏ i, p i)).symm
    simpa using this
  rw [key, map_prod, Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [aeval_def]; exact hp j)

alias main := _root_.GlobalTheory.IntegralPi.isIntegral_pi

end GlobalTheory.IntegralPi
