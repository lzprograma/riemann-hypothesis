module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar

@[expose] public section

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.DefiniteBC

private theorem spehInf_eq_sum_shifted_map (d : ℕ) (m : Multiset ℂ) :
    spehInf d m = ∑ k : Fin d, Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) m := by
  unfold spehInf
  rw [Fin.sum_univ_eq_sum_range (fun k => Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - (k:ℂ))) m) d]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

private theorem infOfWeight_nodup' (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) :
    (GlobalTheory.UnitaryBC.infOfWeight lam).Nodup := by
  apply _root_.GlobalTheory.DefiniteBC.nodup_infOfWeight <;> assumption

private theorem multiset_map_finset_sum {ι : Type*} (s : Finset ι) (g : ℂ → ℂ) (f : ι → Multiset ℂ) :
    Multiset.map g (∑ i ∈ s, f i) = ∑ i ∈ s, Multiset.map g (f i) :=
  map_sum (Multiset.mapAddMonoidHom g) f s

theorem UpperTheory.speh_parameter_strings :
    Strings := by
  intro n c d m lam h
  have hnd := infOfWeight_nodup' n lam
  refine ⟨fun i k => ?_, ?_⟩
  · have hle1 : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ spehInf (d i) (m i) := by
      rw [spehInf_eq_sum_shifted_map]
      exact Finset.single_le_sum (f := fun k : Fin (d i) => Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i))
        (fun _ _ => Multiset.zero_le _) (Finset.mem_univ k)
    have hle2 : spehInf (d i) (m i) ≤ ∑ j, spehInf (d j) (m j) :=
      Finset.single_le_sum (f := fun j => spehInf (d j) (m j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    have hle : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ GlobalTheory.UnitaryBC.infOfWeight lam :=
      h ▸ hle1.trans hle2
    refine ⟨(Multiset.nodup_of_le hle hnd).of_map _, fun z hz => ?_⟩
    have hmem := Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz)
    unfold GlobalTheory.UnitaryBC.infOfWeight at hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    refine ⟨lam.w j - (j:ℕ), ?_⟩
    unfold ex
    push_cast
    linear_combination (-1 : ℂ) * hj
  · rw [← h, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [spehInf_eq_sum_shifted_map, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    unfold ex
    push_cast
    ring
