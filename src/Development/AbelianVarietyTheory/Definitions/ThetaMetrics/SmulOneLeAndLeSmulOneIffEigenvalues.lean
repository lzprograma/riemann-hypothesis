module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology

namespace GlobalTheory

section Weight

variable {κ X : Type*}

noncomputable def lwP₂ (S : Finset κ) (z : κ → ℂ) : ℝ :=
  1 + ∑ j ∈ S, |Real.log ‖z j‖|

def coordDivisor (S : Finset κ) (w : X → κ → ℂ) : Set X :=
  {x | ∃ j ∈ S, w x j = 0}

theorem notMem_coordDivisor {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∉ coordDivisor S w ↔ ∀ j ∈ S, w x j ≠ 0 := by
  simp [coordDivisor]

theorem mem_coordDivisor_iff_prod_eq_zero {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∈ coordDivisor S w ↔ ∏ j ∈ S, w x j = 0 := by
  simp [coordDivisor, Finset.prod_eq_zero_iff]

theorem isClosed_coordDivisor [TopologicalSpace X] (S : Finset κ) {w : X → κ → ℂ}
    (hw : ∀ j ∈ S, Continuous fun x => w x j) : IsClosed (coordDivisor S w) := by
  have : coordDivisor S w = {x | ∏ j ∈ S, w x j = 0} :=
    Set.ext fun _ => mem_coordDivisor_iff_prod_eq_zero
  rw [this]
  exact isClosed_eq (continuous_finsetProd S hw) continuous_const

theorem one_le_logWeight (S : Finset κ) (z : κ → ℂ) : 1 ≤ lwP₂ S z :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logWeight_pos (S : Finset κ) (z : κ → ℂ) : 0 < lwP₂ S z :=
  one_pos.trans_le (one_le_logWeight S z)

theorem mul_logWeight_pow_le (S : Finset κ) (z : κ → ℂ) {C C' : ℝ} {N N' : ℕ} (hC : C ≤ C')
    (hC' : 0 ≤ C') (hN : N ≤ N') : C * lwP₂ S z ^ N ≤ C' * lwP₂ S z ^ N' :=
  mul_le_mul hC (pow_le_pow_right₀ (one_le_logWeight S z) hN)
    (pow_nonneg (logWeight_pos S z).le _) hC'

end Weight

section Growth

variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

def HasLogGrowth (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (f : X → E) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ x ∈ K, x ∉ coordDivisor S w →
    ‖f x‖ ≤ C * lwP₂ S (w x) ^ N

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}

namespace HasLogGrowth

theorem exists_one_le {f : X → E} (hf : HasLogGrowth S w U f) {K : Set X} (hKU : K ⊆ U)
    (hK : IsCompact K) : ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
      ‖f x‖ ≤ C * lwP₂ S (w x) ^ N := by
  obtain ⟨C, N, h⟩ := hf K hKU hK
  exact ⟨max C 1, N, le_max_right _ _, fun x hx hB => (h x hx hB).trans
    (mul_logWeight_pow_le _ _ (le_max_left _ _) (zero_le_one.trans (le_max_right _ _)) le_rfl)⟩

theorem of_continuousOn {f : X → E} (hf : ContinuousOn f U) : HasLogGrowth S w U f := by
  intro K hKU hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
  exact ⟨C, 0, fun x hx _ => by simpa using hC x hx⟩

theorem mul {R : Type*} [SeminormedRing R] {f g : X → R} (hf : HasLogGrowth S w U f)
    (hg : HasLogGrowth S w U g) : HasLogGrowth S w U fun x => f x * g x := by
  intro K hKU hK
  obtain ⟨C, N, hC1, hC⟩ := hf.exists_one_le hKU hK
  obtain ⟨D, M, hD1, hD⟩ := hg.exists_one_le hKU hK
  refine ⟨C * D, N + M, fun x hx hB => (norm_mul_le _ _).trans ?_⟩
  rw [pow_add, mul_mul_mul_comm]
  exact mul_le_mul (hC x hx hB) (hD x hx hB) (norm_nonneg _) ((norm_nonneg _).trans (hC x hx hB))

end HasLogGrowth

end Growth

section Scalar

variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}

namespace IsLogBoundedScalar

end IsLogBoundedScalar

end Scalar

section Entries

variable {κ X l m n : Type*} [TopologicalSpace X]

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}

namespace HasLogGrowthEntries

end HasLogGrowthEntries

end Entries

section MatrixLemmas

variable {m n : Type*}

variable [Fintype n] [DecidableEq n]

variable [Fintype m] [DecidableEq m]



end MatrixLemmas

section Compound

variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]

noncomputable def compoundMatrix (k : ℕ) (A : Matrix l n ℂ) :
    Matrix (Set.powersetCard l k) (Set.powersetCard n k) ℂ :=
  Matrix.of fun I J => (A.submatrix (subsetEnum I) (subsetEnum J)).det

theorem compoundMatrix_mul [Fintype n] (k : ℕ) (A : Matrix l n ℂ) (A' : Matrix n o ℂ) :
    compoundMatrix k (A * A') = compoundMatrix k A * compoundMatrix k A' := by
  ext I J
  exact det_submatrix_mul_eq_sum_minors A A' _ _

theorem compoundMatrix_conjTranspose (k : ℕ) (A : Matrix l n ℂ) :
    compoundMatrix k Aᴴ = (compoundMatrix k A)ᴴ := by
  ext I J
  simp only [compoundMatrix, of_apply, conjTranspose_apply, ← det_conjTranspose,
    conjTranspose_submatrix]

theorem compoundMatrix_one (k : ℕ) : compoundMatrix k (1 : Matrix n n ℂ) = 1 := by
  ext I J
  rcases eq_or_ne I J with rfl | h
  · rw [one_apply_eq, compoundMatrix, of_apply, submatrix_one _ (subsetEnum_injective I), det_one]
  · rw [one_apply_ne h, compoundMatrix, of_apply]
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h
    have h1 : x ∈ range (subsetEnum I) := by rw [range_subsetEnum]; exact hxI
    have h2 : x ∉ range (subsetEnum J) := by rw [range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩

variable [Fintype n]

end Compound

section LogBounded

variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']

variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}

namespace IsLogBounded

variable [Fintype n]

end IsLogBounded

variable [Fintype n]

namespace IsLogBounded


end IsLogBounded


namespace IsLogBounded

variable [Fintype m]


end IsLogBounded

end LogBounded

end GlobalTheory
