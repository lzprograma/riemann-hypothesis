module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct

private theorem ent_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) {c : ℝ}
    (hc : 1 ≤ c) (h : ∀ i j, ‖g.val i j‖ ≤ c) (i j : Fin n) : ‖(emb e g).val i j‖ ≤ c := by
  have hone : ∀ p q : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) p q‖ ≤ c := by
    intro p q
    rw [Matrix.one_apply]
    split_ifs <;> simp [hc, zero_le_one.trans hc]
  show ‖((emb e g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c
  rw [coe_emb, Matrix.add_apply]
  by_cases hi : ∃ k, i = e k
  · by_cases hj : ∃ l, j = e l
    · obtain ⟨k, rfl⟩ := hi
      obtain ⟨l, rfl⟩ := hj
      simp only [matrixExtendByZero_apply, Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff, add_sub_cancel]
      exact h k l
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ i hj, add_zero]
      exact hone i j
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, add_zero]
    exact hone i j

private theorem loc_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) :
    locHeight (emb e g) ≤ locHeight g := by
  apply locHeight_le (one_le_locHeight g)
  · exact ent_le e g (one_le_locHeight g) (norm_apply_le_locHeight g)
  · intro i j
    rw [← map_inv]
    exact ent_le e g⁻¹ (one_le_locHeight g) (norm_inv_apply_le_locHeight g) i j

theorem UpperTheory.height_blockEmbedding_le :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K a), AutomorphicForm.height (emb e g) ≤ AutomorphicForm.height g := by
  classical
  intro K _ _ a n e g
  have hfin : ∀ v, Reduction.finAt v (emb e g) = emb e (Reduction.finAt v g) := by
    intro v
    show Matrix.GeneralLinearGroup.map (Reduction.finEval v) (emb e g) = _
    rw [emb_map]
    rfl
  have hinf : ∀ w, Reduction.infAt w (emb e g) = emb e (Reduction.infAt w g) := by
    intro w
    show Matrix.GeneralLinearGroup.map (Reduction.infEval w) (emb e g) = _
    rw [emb_map]
    rfl
  unfold AutomorphicForm.height
  simp only [hfin, hinf]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀
    · intro w _
      exact pow_nonneg (locHeight_pos _).le _
    · intro w _
      exact pow_le_pow_left₀ (locHeight_pos _).le (loc_le e _) _
  · have h1 := finite_mulSupport_locHeight_finAt (emb e g)
    have h2 := finite_mulSupport_locHeight_finAt g
    simp only [hfin] at h1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx]),
      finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx])]
    apply Finset.prod_le_prod₀
    · intro v _
      exact (locHeight_pos _).le
    · intro v _
      exact loc_le e _
  · exact finprod_nonneg fun v => (locHeight_pos _).le
  · exact (zero_lt_one.trans_le (one_le_prod_locHeight g)).le
