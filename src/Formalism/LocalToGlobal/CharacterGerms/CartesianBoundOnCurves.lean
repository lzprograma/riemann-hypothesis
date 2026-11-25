module

public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

private theorem exists_subring_iff_ge_zero : ∃ R : Subring C, ∀ a, a ∈ R ↔ V.Ge 0 a :=
  ⟨{ carrier := {a | V.Ge 0 a}, mul_mem' := VF.Ge.mul_int, one_mem' := VF.Ge.one,
     add_mem' := VF.Ge.add, zero_mem' := VF.Ge.zero 0, neg_mem' := VF.Ge.neg }, fun _ => Iff.rfl⟩

theorem VF.Ge.prod {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∏ i ∈ s, f i) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  exact (hR _).1 (prod_mem fun i hi => (hR _).2 (h i hi))

theorem det_int (M : Matrix I I C) (h : ∀ i j, V.Ge 0 (M i j)) : V.Ge 0 M.det := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hM : M = (Matrix.of fun a b => (⟨M a b, (hR _).2 (h a b)⟩ : R)).map R.subtype := by
    ext a b
    rfl
  rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hR _).1 (Subtype.mem _)

theorem inv_unit_int {a : C} (h : V.v a = 0) : V.Ge 0 a⁻¹ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at h
    exact WithTop.top_ne_zero h
  have e : V.v a + V.v a⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ ha, AddValuation.map_one]
  rw [h, zero_add] at e
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v a⁻¹
  rw [e, WithTop.coe_zero]

theorem inv_int (M : Matrix I I C) (h : ∀ i j, V.Ge 0 (M i j)) (hd : V.v M.det = 0) :
    ∀ i j, V.Ge 0 (M⁻¹ i j) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hadj : ∀ i j, V.Ge 0 (M.adjugate i j) := by
    have hM : M = (Matrix.of fun a b => (⟨M a b, (hR _).2 (h a b)⟩ : R)).map R.subtype := by
      ext a b
      rfl
    intro i j
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact (hR _).1 (Subtype.mem _)
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hR _).1 (mul_mem ((hR _).2 (inv_unit_int hd)) ((hR _).2 (hadj i j)))

namespace Cart

variable (X : Cart V d I J)

variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}

end Cart

namespace Sys

variable {X : Cart V d I J} (S : Sys X)

theorem mem (c : I) : S.cur c ∈ X.Ty := (S.curve c).1

theorem pure (c : I) : ∀ (i : ℕ) n, X.ty n ≠ X.ty (Sum.inl c) + i → S.cur c i n = 0 := (S.curve c).2.2

theorem cur_zero_inl (c k : I) : S.cur c 0 (Sum.inl k) = S.tan c k := by
  rw [(S.curve c).2.1]
  rfl

theorem be_zero (c : I) (κ : J) : S.cur c 0 (Sum.inr κ) = 0 := by
  rw [(S.curve c).2.1]
  rfl

def U : Matrix I I C := Matrix.of S.tan

theorem U_int (c k : I) : V.Ge 0 (S.U c k) := by
  have := X.t2 _ (S.mem c) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) (Sum.inl k)
  rw [S.cur_zero_inl] at this
  exact this

theorem U_det_ne : S.U.det ≠ 0 := by
  intro h0
  have := S.unimod
  change V.v S.U.det = 0 at this
  rw [h0, AddValuation.map_zero] at this
  exact WithTop.top_ne_zero this

def co (h : I ⊕ J → C) (b : I) : C := ∑ k, h (Sum.inl k) * S.U⁻¹ k b

theorem co_int {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) (b : I) : V.Ge 0 (S.co h b) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hinv := inv_int S.U (fun i j => S.U_int i j) S.unimod
  show V.Ge 0 (∑ k, h (Sum.inl k) * S.U⁻¹ k b)
  exact (hR _).1 (sum_mem fun k _ => mul_mem ((hR _).2 (hh _)) ((hR _).2 (hinv k b)))

theorem co_spec (h : I ⊕ J → C) (k : I) : ∑ b, S.co h b * S.U b k = h (Sum.inl k) := by
  have hU : S.U⁻¹ * S.U = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : ∀ j, ∑ b, S.U⁻¹ j b * S.U b k = (1 : Matrix I I C) j k := fun j => by
    rw [← hU, Matrix.mul_apply]
  simp only [co, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, e, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Sys

theorem lattice_inclusion_forms_injective (X : Cart V d I J) : LatticeInclusionFormsInjective X :=
  fun S c i n => X.bound0 i _ (S.mem c) n

theorem eq16 (X : Cart V d I J) : Eq16 X := by
  intro a u x hx i hi
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · obtain rfl : i = 1 := by omega
    refine ⟨fun k => ?_, fun κ => ?_⟩
    · rw [hx.2 k]
      show ((_ : ℝ) : WithTop ℝ) ≤ V.v 0
      rw [AddValuation.map_zero]
      exact le_top
    · exact (hx.bound_one _).mono (by norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    refine ⟨fun k => (hx.bound j _).mono (by push_cast; linarith), fun κ =>
      (hx.bound j _).mono (by push_cast; linarith [le_max_right (1 : ℝ) ((j : ℝ) + 2 - 1)])⟩

theorem sysExists (X : Cart V d I J) : SysExists X := by
  intro u hu hty hdet
  have hc : ∀ c, ∃ x, X.IsCurve (X.ty (Sum.inl c)) (u c) x := fun c => by
    obtain ⟨x, hx, h0, hp⟩ := X.t4 (X.ty (Sum.inl c)) (u c) (hu c) (fun k hk => hty c k hk)
    exact ⟨x, hx, h0, hp⟩
  choose cur hcur using hc
  exact ⟨⟨u, cur, hcur, hdet⟩, rfl⟩

end Formalism.L2.FormalSeriesBounds
