module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CintTranslate
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

section
@[expose] public section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Fubini

variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

lemma relIndex_prod (H K : AddSubgroup W) (H' K' : AddSubgroup W') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1

lemma exists_fine_prod {A : AddSubgroup W} {A' : AddSubgroup W'} {φ : W × W' → ℂ}
    (h : Nice (A.prod A') φ) :
    ∃ (B : AddSubgroup W) (B' : AddSubgroup W'), B ≤ A ∧ B' ≤ A' ∧ B.relIndex A ≠ 0 ∧
      B'.relIndex A' ≠ 0 ∧ Fine (A.prod A') φ (B.prod B') := by
  obtain ⟨C, hC⟩ := h
  have i1 : (C.comap (AddMonoidHom.inl W W')).relIndex A ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha, A'.zero_mem⟩
  have i2 : (C.comap (AddMonoidHom.inr W W')).relIndex A' ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨A.zero_mem, ha⟩
  refine ⟨C.comap (AddMonoidHom.inl W W'), C.comap (AddMonoidHom.inr W W'),
    fun a ha => (hC.1 ha).1, fun a ha => (hC.1 ha).2, i1, i2, Model.fine_refine hC ?_ ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have := C.add_mem ha hb
    simpa using this
  · rw [relIndex_prod]
    exact mul_ne_zero i1 i2

theorem cint_prod (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ)
    (h : Nice (A.prod A') φ) :
    (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧
      cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  obtain ⟨B, B', hB, hB', i1, i2, hF⟩ := exists_fine_prod h
  let e := QuotientAddGroup.prodEquiv B B'
  have he : ∀ p : W × W', e (QuotientAddGroup.mk p) =
      ((QuotientAddGroup.mk p.1 : W ⧸ B), (QuotientAddGroup.mk p.2 : W' ⧸ B')) := fun _ => rfl
  have hS := hF.2.2.2.image e
  have f1 : ∀ w, Fine A' (fun w' => φ (w, w')) B' := by
    intro w
    refine ⟨hB', i2, fun w' b hb => ?_, (hS.image Prod.snd).subset ?_⟩
    · have := hF.2.2.1 (w, w') (0, b) ⟨B.zero_mem, hb⟩
      simpa using this
    · rintro _ ⟨w', hw', rfl⟩
      exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  have hinv : ∀ w, ∀ b ∈ B, (fun w' => φ (w + b, w')) = fun w' => φ (w, w') := by
    intro w b hb
    funext w'
    have := hF.2.2.1 (w, w') (b, 0) ⟨hb, B'.zero_mem⟩
    simpa using this
  have f2 : Fine A (fun w => cint A' (fun w' => φ (w, w'))) B := by
    refine ⟨hB, i1, fun w b hb => by simp only [hinv w b hb], (hS.image Prod.fst).subset ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have : ∃ w', φ (w, w') ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hw
      show cint A' (fun w' => φ (w, w')) = 0
      rw [Model.cint_eq (f1 w)]
      simp [hn]
    obtain ⟨w', hw'⟩ := this
    exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  refine ⟨fun w => ⟨B', f1 w⟩, ⟨B, f2⟩, ?_⟩
  rw [Model.cint_eq hF, Model.cint_eq f2, relIndex_prod]
  simp only [fun w => Model.cint_eq (f1 w)]
  have h1 : ∀ p : (W ⧸ B) × (W' ⧸ B'), φ (e.symm p).out = φ (p.1.out, p.2.out) := by
    intro p
    have : e.symm p = QuotientAddGroup.mk (p.1.out, p.2.out) := by
      rw [Equiv.symm_apply_eq, he]
      simp
    rw [this, Model.out_mk hF.2.2.1]
  have hfin : (Function.support fun p : (W ⧸ B) × (W' ⧸ B') => φ (p.1.out, p.2.out)).Finite := by
    refine hS.subset ?_
    intro p hp
    refine ⟨_, ⟨(p.1.out, p.2.out), hp, rfl⟩, ?_⟩
    rw [he]; simp
  have h2 : (∑ᶠ c : (W × W') ⧸ B.prod B', φ c.out) =
      ∑ᶠ (a : W ⧸ B) (b : W' ⧸ B'), φ (a.out, b.out) := by
    rw [← finsum_comp_equiv e.symm, finsum_congr h1, finsum_curry _ hfin]
  rw [h2]
  simp only [div_eq_mul_inv]
  rw [← finsum_mul]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.IdxInt.Fubini
end
end


@[expose] public section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

