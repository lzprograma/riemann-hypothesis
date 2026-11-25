module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Real

@[expose] public section

open scoped Topology

namespace GlobalTheory.CompanionTheory.SW.TailCut

theorem tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  intro ι _ a S S' hsum hSS'
  have htail : Multipliable (fun v : {v // v ∉ S'} => a v.1) := by
    simpa [Function.comp_def] using
      Real.multipliable_one_add_of_summable (hsum.of_abs.subtype (· ∉ S'))
  have hd : Disjoint (↑(S' \ S) : Set ι) (↑S')ᶜ :=
    Set.disjoint_compl_right_iff_subset.mpr Finset.sdiff_subset
  have h := HasProd.mul_disjoint hd ((S' \ S).hasProd a) htail.hasProd
  rw [Finset.coe_sdiff, ← compl_sdiff_compl,
    Set.sdiff_union_of_subset (Set.compl_subset_compl.mpr (Finset.coe_subset.mpr hSS'))] at h
  exact h.tprod_eq

end GlobalTheory.CompanionTheory.SW.TailCut
