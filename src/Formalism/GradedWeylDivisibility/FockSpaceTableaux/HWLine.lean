module

public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility

theorem highest_weight_line : HWLine := by
  intro K _ _ r n hn ν hν f hf hraise
  have hfP := (dualWeylPoint K r n ν f).mp hf
  have hhP := (dualWeylPoint K r n ν _).mp (hwMem K r n hn ν hν)
  let c := AddMonoidAlgebra.coeff f (lhwline_mnu hn ν)
  refine ⟨c, sub_eq_zero.mp ?_⟩
  apply lhwline_vanish
  · intro a b hab
    rw [map_sub, map_smul, lhwline_rowGen_eq a b f (hraise a b hab),
      lhwline_rowGen_eq a b (hw K hn ν) (fun k hk => hwRaise K r n hn ν a b k hab hk)]
    simp [Polynomial.smul_C]
  · intro l j hlj c'
    rw [map_sub, map_smul, hfP.2 l j hlj c', hhP.2 l j hlj c']
  · intro D hD
    have diag := lhwline_diag hn ν (hw K hn ν) hhP.1
    suffices h : AddMonoidAlgebra.coeff (hw K hn ν) (lhwline_mnu hn ν) = 1 by
      rw [Algebra.smul_def]
      change eval D (f - C c * hw K hn ν) = 0
      simp [c, lhwline_diag hn ν f hfP.1 D hD, diag D hD, h]
    simpa only [show (∏ v, idPoint K r n v ^ (lhwline_mnu hn ν) v) = 1 from
        Finset.prod_eq_one fun ⟨a, j⟩ _ => by
          by_cases h : a.val = j.val <;> simp [lhwline_mnu_apply, idPoint, h],
      mul_one, show eval (idPoint K r n) (hw K hn ν) = 1 by simp [hw, eval_idPoint_lpMinor]] using
      (diag (idPoint K r n) (fun a j h => by simp [idPoint, h])).symm

end Formalism.GradedWeylDivisibility
