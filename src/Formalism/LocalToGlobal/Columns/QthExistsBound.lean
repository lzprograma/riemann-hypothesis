module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.TwQCmp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Val

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem qth_intAt_iff (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  apply _root_.GlobalTheory.CharVal.intAt_iff <;> assumption

theorem qth_exists_bound (x : E) : ∃ k : ℕ, P.valuation E x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : P.valuation E x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log (P.valuation E x)).toNat, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hx]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat _)

theorem qth_bound {m : ℕ} (M : Matrix (Fin m) (Fin m) E) : ∃ a : ℕ, ∀ i j, P.valuation E (M i j) ≤ WithZero.exp (a : ℤ) := by
  choose k hk using fun ij : Fin m × Fin m => qth_exists_bound P (M ij.1 ij.2)
  refine ⟨Finset.univ.sup k, fun i j => (hk (i, j)).trans ?_⟩
  exact WithZero.exp_le_exp.2 (Nat.cast_le.2 (Finset.le_sup (f := k) (Finset.mem_univ (i, j))))

theorem qth_conj_le {m : ℕ} (A Z B : Matrix (Fin m) (Fin m) E) (a b N : ℤ)
    (hA : ∀ i j, P.valuation E (A i j) ≤ WithZero.exp a) (hZ : ∀ i j, P.valuation E (Z i j) ≤ WithZero.exp (-N))
    (hB : ∀ i j, P.valuation E (B i j) ≤ WithZero.exp b) (i j : Fin m) :
    P.valuation E ((A * Z * B) i j) ≤ WithZero.exp (a + -N + b) := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul, WithZero.exp_add]
  refine mul_le_mul' ?_ (hB k j)
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' (hA i l) (hZ l k)

end Val

end Formalism.L2.Col
