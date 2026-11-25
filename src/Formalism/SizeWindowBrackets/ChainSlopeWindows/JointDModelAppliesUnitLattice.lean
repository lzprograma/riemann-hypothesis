module

public import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Formalism.HarderNarasimhan.ShiftInvariance

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf, Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice

-- ===== clump member: Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf =====
-- clump-header: {"m": "Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf", "h": "module\n\npublic import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds\nimport Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Algebra.BigOperators.Field\npublic import Mathlib.Analysis.CStarAlgebra.Basic\npublic import Mathlib.Basic.Complex.BigOperators\n\n"}
section -- clump:auto
@[expose] public section
open Matrix
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section

section HS
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
lemma hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma trace_conjTranspose_mul_self (M : Matrix m n ℂ) :
    (Mᴴ * M).trace = ((hsSq M : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    hsSq, Complex.ofReal_sum]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; rfl
lemma hsSq_eq_re (M : Matrix m n ℂ) : hsSq M = (Mᴴ * M).trace.re := by
  rw [trace_conjTranspose_mul_self, Complex.ofReal_re]
lemma hsSq_conjTranspose (M : Matrix m n ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]; exact Finset.sum_comm
lemma hsSq_smul (c : ℂ) (M : Matrix m n ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  simp only [hsSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]
end HS

section CS
variable {m n : Type} [Fintype m] [Fintype n]
private theorem sum_norm_mul_le_hsNorm_mul (A B : Matrix m n ℂ) :
    ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ ≤ hsNorm A * hsNorm B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  simp only [Fintype.sum_prod_type] at h
  rw [hsNorm, hsNorm, ← Real.sqrt_mul (hsSq_nonneg A)]; exact Real.le_sqrt_of_sq_le h

lemma norm_trace_mul_le (X : Matrix m n ℂ) (Y : Matrix n m ℂ) :
    ‖(X * Y).trace‖ ≤ hsNorm X * hsNorm Y := by
  rw [← show hsNorm Yᵀ = hsNorm Y by
    simp only [hsNorm, hsSq, Matrix.transpose_apply]; exact congrArg Real.sqrt Finset.sum_comm]
  refine le_trans ?_ (sum_norm_mul_le_hsNorm_mul X Yᵀ)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ =>
    (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))

lemma hsSq_one (n : ℕ) : hsSq (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp [hsSq, Matrix.one_apply, apply_ite]
lemma hsNorm_nonneg (M : Matrix m n ℂ) : 0 ≤ hsNorm M := Real.sqrt_nonneg _
lemma hsNorm_sq (M : Matrix m n ℂ) : hsNorm M ^ 2 = hsSq M := Real.sq_sqrt (hsSq_nonneg M)
lemma hsSq_add_le (A B : Matrix m n ℂ) : hsSq (A + B) ≤ (hsNorm A + hsNorm B) ^ 2 := by
  calc hsSq (A + B)
      ≤ ∑ i, ∑ j, (‖A i j‖ + ‖B i j‖) ^ 2 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum
        fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A i j) (B i j)) 2
    _ = hsSq A + hsSq B + 2 * ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ := by
        simp only [hsSq, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ (hsNorm A + hsNorm B) ^ 2 := by
        rw [add_sq, hsNorm_sq, hsNorm_sq]; linarith [sum_norm_mul_le_hsNorm_mul A B]
lemma hsNorm_le_of_sq (M : Matrix m n ℂ) {e x : ℝ} (he : 0 ≤ e) (h : hsSq M ≤ e * x) :
    hsNorm M ≤ Real.sqrt e * Real.sqrt x := by
  rw [hsNorm, ← Real.sqrt_mul he]; exact Real.sqrt_le_sqrt h
end CS

theorem traceLowerBound : TraceLower := fun n K => by
  have h2 := norm_trace_mul_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  have h4 := Complex.re_le_norm (-((1 : Matrix (Fin n) (Fin n) ℂ) * (K - 1)).trace)
  rw [hsNorm, hsSq_one, one_mul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin] at h2
  rw [Complex.neg_re, norm_neg, one_mul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin,
    Complex.sub_re, Complex.natCast_re] at h4; linarith
lemma hsSq_le_of_sub_one (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) :
    hsSq K ≤ (Real.sqrt n + hsNorm (K - 1)) ^ 2 := by
  have h := hsSq_add_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  rwa [show (1 : Matrix (Fin n) (Fin n) ℂ) + (K - 1) = K by abel, hsNorm, hsSq_one] at h

section Fam
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
lemma Kd_eq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) (u : ι) :
    Kd B ga u = ((ga u : ℝ) : ℂ) • ((B u)ᴴ * B u) := by
  let _ := ‹Fintype ι›; unfold Kd Kp; rw [Real.sqrt_mul_self (hga u)]
lemma trace_Qm (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga).trace = ∑ u, (Kd B ga u).trace := by
  unfold Qm; rw [Matrix.trace_sum]; refine Finset.sum_congr rfl fun u _ => ?_
  rw [Kd_eq B ga hga u, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_mul_comm]
lemma hsSq_Kp (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    (u u' : ι) : hsSq (Kp B ga u u') = ga u * ga u' * hsSq ((B u)ᴴ * B u') := by
  let _ := ‹Fintype ι›
  rw [Kp, hsSq_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_nonneg (hga u) (hga u'))]
lemma trace_Qm_sq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga * Qm B ga).trace = (((∑ u, ∑ u', hsSq (Kp B ga u u') : ℝ)) : ℂ) := by
  unfold Qm; simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  rw [Matrix.trace_mul_comm]
  simp only [hsSq_Kp B ga hga u u', Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, ← trace_conjTranspose_mul_self, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Complex.ofReal_mul]
  rw [Matrix.mul_assoc (B u), Matrix.trace_mul_comm (B u), Matrix.trace_mul_comm ((B u')ᴴ * B u)]
  simp only [Matrix.mul_assoc]; ring

lemma Rs_nonneg (d : ι → ℕ) : 0 ≤ Rs d := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
lemma trQ_lower (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {e0 : ℝ} (he : 0 ≤ e0) (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  rw [trace_Qm B ga hga, Complex.re_sum, Rs, Finset.mul_sum]; refine Finset.sum_le_sum fun u _ => ?_
  have h2 := mul_le_mul_of_nonneg_left (hsNorm_le_of_sq _ he (hK u)) (Real.sqrt_nonneg (d u : ℝ))
  rw [show Real.sqrt (d u : ℝ) * (Real.sqrt e0 * Real.sqrt (d u : ℝ)) =
      Real.sqrt e0 * (Real.sqrt (d u : ℝ) * Real.sqrt (d u : ℝ)) by ring,
    Real.mul_self_sqrt (Nat.cast_nonneg _)] at h2
  linarith [traceLowerBound (d u) (Kd B ga u)]

lemma trQsq_upper (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar η0 e0 : ℝ} (hD : 0 < Dstar) (hη : -1 ≤ η0) (he : 0 ≤ e0)
    (hP : ∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar)
    (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (Qm B ga * Qm B ga).trace.re ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
  classical
  have hη' : 0 ≤ 1 + η0 := by linarith
  have hdiag (u : ι) : hsSq (Kp B ga u u) ≤ (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) := by
    rw [← Real.sq_sqrt (Nat.cast_nonneg (d u)), ← mul_pow]
    exact (hsSq_le_of_sub_one (d u) (Kd B ga u)).trans (pow_le_pow_left₀
      (add_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg _))
      (by linarith [hsNorm_le_of_sq _ he (hK u)]) 2)
  rw [trace_Qm_sq B ga hga, Complex.ofReal_re]
  calc ∑ u, ∑ u', hsSq (Kp B ga u u')
      ≤ ∑ u, ∑ u', ((1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar +
          if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => by
          by_cases h : u = u'
          · subst h; rw [ite_eq_left rfl]; linarith [hdiag u,
              show 0 ≤ (1 + η0) * (d u : ℝ) * (d u : ℝ) / Dstar by positivity]
          · rw [ite_eq_right h, add_zero]; exact hP u u' h
    _ = (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [← Finset.mul_sum, ← Rs]; congr 1; simp only [Rs, sq, Finset.sum_mul, Finset.mul_sum,
          Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end Fam

section Compress
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]
lemma proj_herm (V : Matrix m k ℂ) : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
  let _ := (‹Fintype m›, ‹DecidableEq k›)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
lemma proj_idem (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  have hP : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]; abel
lemma hsSq_split (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq M = hsSq (Vᴴ * M) + hsSq ((1 - V * Vᴴ) * M) := by
  rw [hsSq_eq_re M, hsSq_eq_re (Vᴴ * M), hsSq_eq_re ((1 - V * Vᴴ) * M), ← Complex.add_re,
    ← Matrix.trace_add]; congr 2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    proj_herm V, show Mᴴ * (1 - V * Vᴴ) * ((1 - V * Vᴴ) * M) =
      Mᴴ * ((1 - V * Vᴴ) * (1 - V * Vᴴ)) * M by simp only [Matrix.mul_assoc], proj_idem V hV]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
lemma hsSq_left_le (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq (Vᴴ * M) ≤ hsSq M := by linarith [hsSq_split V hV M, hsSq_nonneg ((1 - V * Vᴴ) * M)]
end Compress

lemma hsSq_compress {a b c e : ℕ} (V : Matrix (Fin a) (Fin c) ℂ) (hV : Vᴴ * V = 1)
    (W : Matrix (Fin b) (Fin e) ℂ) (hW : Wᴴ * W = 1) (M : Matrix (Fin a) (Fin b) ℂ) :
    hsSq (Vᴴ * M * W) ≤ hsSq M := by
  have h1 := hsSq_left_le W hW (Vᴴ * M)ᴴ
  rw [← Matrix.conjTranspose_mul, hsSq_conjTranspose, hsSq_conjTranspose] at h1
  exact h1.trans (hsSq_left_le V hV M)
lemma trace_proj (n k : ℕ) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ).trace = ((((n : ℝ) - (k : ℝ)) : ℝ) : ℂ) := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, hV, Matrix.trace_one, Matrix.trace_one,
    Fintype.card_fin, Fintype.card_fin]; push_cast; ring

lemma ram_gap (n k : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ)
    (hV : Vᴴ * V = 1) {e0 : ℝ} (he : 0 ≤ e0) (hK : hsSq (K - 1) ≤ e0 * n) :
    0 ≤ (n : ℝ) - k ∧ K.trace.re - (Vᴴ * K * V).trace.re ≤
      ((n : ℝ) - k) + Real.sqrt ((n : ℝ) - k) * (Real.sqrt e0 * Real.sqrt n) := by
  have hnk : hsSq (1 - V * Vᴴ) = (n : ℝ) - k := Complex.ofReal_injective <| by
    have h := trace_conjTranspose_mul_self (1 - V * Vᴴ)
    rwa [proj_herm V, proj_idem V hV, trace_proj n k V hV, eq_comm] at h
  refine ⟨hnk ▸ hsSq_nonneg _, ?_⟩
  have hre := congrArg Complex.re (show K.trace - (Vᴴ * K * V).trace =
      (1 - V * Vᴴ).trace + ((K - 1) * (1 - V * Vᴴ)).trace by
    rw [Matrix.trace_mul_comm (Vᴴ * K) V, ← Matrix.mul_assoc, Matrix.trace_mul_comm (V * Vᴴ) K]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub]
    ring)
  have hcs := norm_trace_mul_le (K - 1) (1 - V * Vᴴ)
  rw [show hsNorm (1 - V * Vᴴ) = Real.sqrt ((n : ℝ) - k) by rw [hsNorm, hnk]] at hcs
  rw [Complex.sub_re, Complex.add_re, trace_proj n k V hV, Complex.ofReal_re] at hre
  linarith [Complex.re_le_norm (((K - 1) * (1 - V * Vᴴ)).trace), hcs,
    mul_le_mul_of_nonneg_right (hsNorm_le_of_sq _ he hK) (Real.sqrt_nonneg ((n : ℝ) - k))]

lemma num_main {s η0 η1 a : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hη0 : -1 ≤ η0) (hη0' : η0 ≤ s / 2)
    (hη1' : η1 ≤ s / 2) (_hL : 0 ≤ 1 + η1) (ha : 0 ≤ a) (ha' : a ≤ s / 2) :
    (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s) ≤ (1 + 5 * s) * (1 - a) ^ 2 := by
  have hs' : 0 ≤ 1 / 4 - s := by linarith
  calc (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s)
      ≤ (1 + s / 2) * ((1 + s / 2) + (1 + s / 2) ^ 2 * s) :=
        (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (by linarith)
          (mul_nonneg (sq_nonneg _) hs0.le))).trans (mul_le_mul_of_nonneg_left (add_le_add
            (by linarith) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith)
              (by linarith) 2) hs0.le)) (by linarith))
    _ ≤ (1 + 5 * s) * (1 - s / 2) ^ 2 := by
        rw [← sub_nonneg, show (1 + 5 * s) * (1 - s / 2) ^ 2 - (1 + s / 2) *
          ((1 + s / 2) + (1 + s / 2) ^ 2 * s) = s / 8 * (3 + 52 * (1 / 4 - s) +
          15 / 4 * s ^ 2 + (1 / 4 - s) * s ^ 2) by ring]; positivity
    _ ≤ (1 + 5 * s) * (1 - a) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by linarith)

lemma num_ram {s a t : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 20) (ha : 0 ≤ a) (ha' : a ≤ s / 2)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 + 5 * s) * (1 - a) ^ 2 ≤ (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 := by
  have hb0 : 0 ≤ 1 - a := by linarith
  have hP0 : 0 ≤ 1 + 5 * s + 3 * t := by linarith
  have hk : 0 ≤ 3 * (1 - a) - 2 * (1 + 5 * s + 3 * t) * (t + a) := by
    linarith [mul_le_mul_of_nonneg_right
      (by linarith : 2 * (1 + 5 * s + 3 * t) ≤ 11 / 2) (by linarith : 0 ≤ t + a)]
  rw [← sub_nonneg, show (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 -
    (1 + 5 * s) * (1 - a) ^ 2 = t * (1 - a) * (3 * (1 - a) - 2 * (1 + 5 * s + 3 * t) * (t + a)) +
    (1 + 5 * s + 3 * t) * (t ^ 2 + t * a) ^ 2 by ring]; positivity

lemma num_step {T2 T1 R Dst D X L c b : ℝ} (hD : 0 < D) (hDs : 0 < Dst) (hDD : D ≤ L * Dst)
    (hX : 0 ≤ X) (hT2 : T2 ≤ R ^ 2 / Dst * X) (hb : 0 ≤ b * R) (hT1 : b * R ≤ T1)
    (hc : L * X ≤ c * b ^ 2) (hc0 : 0 ≤ c) : T2 ≤ c * T1 ^ 2 / D := by
  rw [le_div_iff₀ hD]; refine le_of_mul_le_mul_right ?_ hDs
  rw [div_mul_eq_mul_div, le_div_iff₀ hDs] at hT2
  linarith [mul_le_mul_of_nonneg_right hT2 hD.le,
    mul_le_mul_of_nonneg_left hDD (mul_nonneg (sq_nonneg R) hX),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (sq_nonneg R)) hDs.le,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hT1 2) hc0) hDs.le,
    show T2 * D * Dst = T2 * Dst * D by ring, show R ^ 2 * X * (L * Dst) = R ^ 2 * (L * X) * Dst by ring,
    show R ^ 2 * (c * b ^ 2) * Dst = c * (b * R) ^ 2 * Dst by ring]

section Ram
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
lemma Kp_ram (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (u u' : ι) : Kp (Bram B V) ga u u' = (V u)ᴴ * Kp B ga u u' * V u' := by
  let _ := ‹Fintype ι›
  simp only [Kp, Bram, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
lemma Kd_ram_sub (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (hV : Isom V) (u : ι) :
    Kd (Bram B V) ga u - 1 = (V u)ᴴ * (Kd B ga u - 1) * V u := by
  rw [Kd, Kp_ram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV u, Kd]

theorem compressTraceLowerBound : RamTrace :=
  fun ι _ D d r B V ga de e0 hV hga hde he hK hsum => by
  have hu (u : ι) := ram_gap (d u) (r u) (Kd B ga u) (V u) (hV u) he (hK u)
  have hCS : ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) ≤ Real.sqrt de * Rs d := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun u => Real.sqrt ((d u : ℝ) - r u)) (fun u => Real.sqrt (d u))
    simp only [fun u => Real.sq_sqrt (hu u).1, fun u => Real.sq_sqrt (Nat.cast_nonneg (d u))] at h
    exact (Real.le_sqrt_of_sq_le h).trans <|
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hsum (Rs_nonneg d))).trans_eq <| by
        rw [mul_assoc, Real.sqrt_mul hde, Real.sqrt_mul_self (Rs_nonneg d)]
  have hsumu := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
    (show Kd (Bram B V) ga u = _ from Kp_ram B V ga u u) ▸ (hu u).2
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    show ∑ u, Real.sqrt ((d u : ℝ) - r u) * (Real.sqrt e0 * Real.sqrt (d u)) =
      Real.sqrt e0 * ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring] at hsumu
  rw [trace_Qm B ga hga, trace_Qm (Bram B V) ga hga, Complex.re_sum, Complex.re_sum,
    Real.sqrt_mul hde e0]; linarith [mul_le_mul_of_nonneg_left hCS (Real.sqrt_nonneg e0)]

theorem compressDiagDefectBound : CompressDiagDefectBound :=
  fun ι _ D d r B V ga de e0 hV hde he hK hsum => by
  have h1 : (1 - de) * Rs d ≤ Rs r := by
    unfold Rs at hsum ⊢; rw [Finset.sum_sub_distrib] at hsum; linarith
  have h2 : Rs d ≤ 2 * Rs r := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤ 1 - de) (Rs_nonneg d)]
  refine ⟨h1, ?_⟩; unfold F2
  calc ∑ u, hsSq (Kd (Bram B V) ga u - 1)
      ≤ ∑ u, e0 * (d u : ℝ) := Finset.sum_le_sum fun u _ => by
        rw [Kd_ram_sub B V ga hV u]; exact (hsSq_compress (V u) (hV u) (V u) (hV u) _).trans (hK u)
    _ = e0 * Rs d := by rw [Rs, Finset.mul_sum]
    _ ≤ 2 * e0 * Rs r := by linarith [mul_le_mul_of_nonneg_left h2 he]

lemma cor_common (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar sg η0 η1 e0 : ℝ} (hD : 0 < Dstar) (hs0 : 0 < sg) (hs : sg ≤ 1 / 4) (hR : Dstar / sg ≤ Rs d)
    (hη0 : -1 ≤ η0) (he : 0 ≤ e0) (ha' : Real.sqrt e0 ≤ sg / 2) (hS : InputS B ga Dstar η0 η1 e0) :
    0 < (D : ℝ) ∧ 0 ≤ 1 + η1 ∧ 0 < Rs d ∧ (Qm B ga * Qm B ga).trace.re ≤
      Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg) ∧
      (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  obtain ⟨hP, hK, hDD⟩ := hS
  have hT : 0 < Rs d := lt_of_lt_of_le (div_pos hD hs0) hR; have hF1 := trQ_lower B ga hga he hK
  have hDpos : 0 < (D : ℝ) := by
    rcases Nat.eq_zero_or_pos D with rfl | h0
    · simp only [Matrix.trace_fin_zero, Complex.zero_re] at hF1
      linarith [mul_pos (by linarith : 0 < 1 - Real.sqrt e0) hT]
    · exact_mod_cast h0
  have hTT : Rs d ≤ Rs d ^ 2 / Dstar * sg := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    exact (mul_le_mul_of_nonneg_left ((div_le_iff₀ hs0).1 hR) hT.le).trans_eq (by ring)
  refine ⟨hDpos, (mul_nonneg_iff_of_pos_right hD).mp (hDpos.le.trans hDD), hT, ?_, hF1⟩
  calc (Qm B ga * Qm B ga).trace.re
      ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d :=
        trQsq_upper B ga hga hD hη0 he hP hK
    _ ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * (Rs d ^ 2 / Dstar * sg) := by gcongr
    _ = Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg) := by ring

theorem compressTraceSquareBound : CompressTraceSquareBound :=
  fun ι _ D d r B V ga Dstar sg η0 η1 e0 de hV hga hD hs0 hs hR hη0 hη0' hη1' he ha' hde0 hde hsum hS => by
  obtain ⟨hDpos, hL, hT, hF2, _⟩ := cor_common B ga hga hD hs0 (by linarith) hR hη0 he ha' hS
  obtain ⟨_, hK, hDD⟩ := hS
  have hlow := compressTraceLowerBound ι D d r B V ga de e0 hV hga hde0 he hK hsum
  have hT2c : (Qm (Bram B V) ga * Qm (Bram B V) ga).trace.re ≤ (Qm B ga * Qm B ga).trace.re := by
    rw [trace_Qm_sq (Bram B V) ga hga, trace_Qm_sq B ga hga, Complex.ofReal_re, Complex.ofReal_re]
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => by
      rw [Kp_ram]; exact hsSq_compress (V u) (hV u) (V u') (hV u') _
  have ht0 := Real.sqrt_nonneg de; have ha0 := Real.sqrt_nonneg e0
  have ht1 : Real.sqrt de ≤ 1 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have hT1' : (1 - Real.sqrt e0 - Real.sqrt de ^ 2 - Real.sqrt de * Real.sqrt e0) * Rs d ≤
      (Qm (Bram B V) ga).trace.re := by
    rw [Real.sqrt_mul hde0 e0] at hlow; rw [Real.sq_sqrt hde0]; linarith
  exact num_step hDpos hD hDD (add_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hs0.le))
    (hT2c.trans hF2)
    (mul_nonneg (by rw [Real.sq_sqrt hde0]; linarith [mul_le_mul_of_nonneg_right ht1 ha0]) hT.le)
    hT1' (by linarith [num_main hs0 (by linarith) hη0 hη0' hη1' hL ha0 ha',
      num_ram hs0 hs ha0 ha' ht0 ht1]) (by linarith)
end Ram

end
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf =====

-- ===== clump member: Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice =====
-- clump-header: {"m": "Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice", "h": "module\n\npublic import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv\npublic import Mathlib.RingTheory.Coalgebra.IsFrobenius\npublic import Mathlib.RingTheory.HopfAlgebra.Basic\npublic import Formalism.HarderNarasimhan.ShiftInvariance\npublic import Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)

section Lin

variable {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o]

theorem to_euclidean_lin_mul (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B :=
  Matrix.toLpLin_mul 2 2 2 A B

theorem to_euclidean_lin_one : Matrix.toEuclideanLin (1 : Matrix n n ℂ) = LinearMap.id :=
  Matrix.toLpLin_one 2

theorem to_euclidean_lin_trace (A : Matrix n n ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ n) (Matrix.toEuclideanLin A) = A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

theorem to_euclidean_lin_adjoint_eq (A : Matrix m n ℂ) :
    LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin Aᴴ :=
  (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

theorem hs_norm_sq_to_euclidean_lin (A : Matrix m n ℂ) : hs2 (Matrix.toEuclideanLin A) = hsSq A := by
  unfold hs2
  rw [to_euclidean_lin_adjoint_eq, ← to_euclidean_lin_mul, to_euclidean_lin_trace, HilbertSchmidtNormSquare.hsSq_eq_re]

theorem frame_kernel_to_lin_sub_id (c : ℝ) (A : Matrix m n ℂ) :
    frK c (Matrix.toEuclideanLin A) - LinearMap.id
      = Matrix.toEuclideanLin ((c : ℂ) • (Aᴴ * A) - 1) := by
  unfold frK
  rw [to_euclidean_lin_adjoint_eq, ← to_euclidean_lin_mul, map_sub, map_smul, to_euclidean_lin_one]

end Lin

theorem weighted_gram_eq_smul {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ)
    (ga : I → ℝ) (i : I) (hi : 0 ≤ ga i) : KdG B ga i = ((ga i : ℝ) : ℂ) • ((B i)ᴴ * B i) := by
  unfold KdG KpG
  rw [Real.sqrt_mul_self hi]

theorem hilbert_schmidt_transfer_holds : BridgeHS := by
  intro I α _ ι _ _ B ga i hi
  classical
  rw [frame_kernel_to_lin_sub_id, hs_norm_sq_to_euclidean_lin, weighted_gram_eq_smul B ga i hi]

theorem weighted_frame_operator_to_lin {I α : Type} [Fintype I] [Fintype α] [DecidableEq α] {ι : I → Type}
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    frQ ga (fun i => Matrix.toEuclideanLin (B i)) = Matrix.toEuclideanLin (QmG B ga) := by
  unfold frQ QmG

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, to_euclidean_lin_mul, to_euclidean_lin_adjoint_eq]

theorem quadratic_transfer_holds : BridgeQ := by
  intro I α _ _ _ ι _ _ B ga
  rw [weighted_frame_operator_to_lin, ← to_euclidean_lin_mul, to_euclidean_lin_trace, to_euclidean_lin_trace]
  exact ⟨rfl, rfl⟩

theorem hs_sq_reindex {m n m' n' : Type} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) : hsSq (Matrix.reindex e f M) = hsSq M := by
  unfold HilbertSchmidtNormSquare.hsSq
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.symm.sum_comp]
  rfl

theorem matrix_trace_reindex {m m' : Type} [Fintype m] [Fintype m'] (e : m ≃ m')
    (M : Matrix m m ℂ) : (Matrix.reindex e e M).trace = M.trace := by
  unfold Matrix.trace
  rw [← e.symm.sum_comp]
  rfl

theorem kernel_matrix_reindex {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i j : I) :
    HilbertSchmidtNormSquare.Kp (toFin B) ga i j
      = Matrix.reindex (Fintype.equivFin (ι i)) (Fintype.equivFin (ι j)) (KpG B ga i j) := by
  unfold HilbertSchmidtNormSquare.Kp KpG toFin
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_smul, Pi.smul_apply]

theorem weighted_gram_sub_one_reindex {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I) :
    HilbertSchmidtNormSquare.Kd (toFin B) ga i - 1
      = Matrix.reindex (Fintype.equivFin (ι i)) (Fintype.equivFin (ι i)) (KdG B ga i - 1) := by
  unfold HilbertSchmidtNormSquare.Kd KdG
  rw [kernel_matrix_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_sub, Matrix.submatrix_one_equiv, Pi.sub_apply]

theorem quadratic_matrix_fin_reindex {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    HilbertSchmidtNormSquare.Qm (toFin B) ga
      = Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin α) (QmG B ga) := by
  unfold HilbertSchmidtNormSquare.Qm QmG toFin

  rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_smul, Pi.smul_apply]

theorem transfer_fin_index_holds : BridgeFin := by
  intro I α _ _ ι _ _ B ga
  refine ⟨fun i j => ?_, fun i => ?_, ?_, ?_, rfl⟩
  · rw [kernel_matrix_reindex, hs_sq_reindex]
  · rw [weighted_gram_sub_one_reindex, hs_sq_reindex]
  · rw [quadratic_matrix_fin_reindex, matrix_trace_reindex]
  · rw [quadratic_matrix_fin_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact matrix_trace_reindex (Fintype.equivFin α) (QmG B ga * QmG B ga)

theorem input_size_transfer_holds : BridgeInputS := by
  intro I α _ _ ι _ _ B ga Dstar η0 η1 e0
  obtain ⟨h1, h2, -, -, -⟩ := transfer_fin_index_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.InputS InputSG
  simp only [h1, h2]

theorem ramification_transfer_holds : BridgeRam := by
  intro I α _ ιf ι _ _ _ Bf Vr
  constructor
  · funext i
    unfold toFin HilbertSchmidtNormSquare.Bram toFinV
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  · unfold HilbertSchmidtNormSquare.Isom toFinV
    refine forall_congr' fun i => ?_
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    constructor
    · intro h
      have := congrArg (fun M => M.submatrix (Fintype.equivFin (ι i)) (Fintype.equivFin (ι i))) h
      simpa using this
    · intro h
      rw [h, Matrix.submatrix_one_equiv]

theorem first_family_transfer_holds : FrameTraceRatioFinEquiv := by
  intro I α _ _ ι _ _ B ga η
  classical
  obtain ⟨-, -, h3, h4, -⟩ := transfer_fin_index_holds I α ι B ga
  obtain ⟨q1, q2⟩ := quadratic_transfer_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.F1 FrameTraceRatioLinear
  rw [h3, h4, q1, q2]

theorem second_family_transfer_holds : FrameDeviationFinEquiv := by
  intro I α _ _ ι _ _ B ga e hga
  obtain ⟨-, h2, -, -, h5⟩ := transfer_fin_index_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.F2 FrameDeviationLinear
  rw [h5]
  simp only [h2, fun i => hilbert_schmidt_transfer_holds I α ι B ga i (hga i)]
  rfl

theorem ramification_linear_case_holds : RamLin := by
  intro I α _ _ ιf ι _ _ _ _ Bf Vr ga Dstar sg η0 η1 e0 de hV hga hD hsg hsg20 hR h0 h0' h1 he0 hse
    hde hde4 hcor hS
  have hS' := (input_size_transfer_holds I α ιf Bf ga Dstar η0 η1 e0).2 hS
  obtain ⟨hB, hI⟩ := ramification_transfer_holds I α ιf ι Bf Vr
  have hV' := hI.2 hV
  have f1 := HilbertSchmidtNormSquare.compressTraceSquareBound I (Fintype.card α) (fun i => Fintype.card (ιf i))
    (fun i => Fintype.card (ι i)) (toFin Bf) (toFinV Vr) ga Dstar sg η0 η1 e0 de hV' hga hD hsg hsg20
    hR h0 h0' h1 he0 hse hde hde4 hcor hS'
  obtain ⟨hRr, f2⟩ := HilbertSchmidtNormSquare.compressDiagDefectBound I (Fintype.card α) (fun i => Fintype.card (ιf i))
    (fun i => Fintype.card (ι i)) (toFin Bf) (toFinV Vr) ga de e0 hV' (by linarith) he0 hS'.2.1 hcor
  rw [← hB] at f1 f2
  refine ⟨(first_family_transfer_holds I α ι _ ga _).1 f1, (second_family_transfer_holds I α ι _ ga _ hga).1 f2, ?_, ?_⟩
  · have hs := Real.sq_sqrt he0
    have hn := Real.sqrt_nonneg e0
    nlinarith
  · have hpos : (0 : ℝ) < RsG ιf := lt_of_lt_of_le (div_pos hD hsg) hR
    have hpos' : (0 : ℝ) < HilbertSchmidtNormSquare.Rs (fun i => Fintype.card (ι i)) := by
      refine lt_of_lt_of_le ?_ hRr
      exact mul_pos (by linarith) hpos
    unfold HilbertSchmidtNormSquare.Rs at hpos'
    exact_mod_cast hpos'

theorem flat_lattice_theorem_holds : TheoremFLat := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ hG hN hγ hF2 he he4 hF1 hη
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hG
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  exact theoremF K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ g1 g2 g3 g4 g5 g6 g7 g8
    g9 g10 g11 n1 n2 n3 n4 n5 g12 g13 g14 g15 hγ hF2 he he4 hF1 hη

theorem sharp_flat_lattice_theorem_holds :
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → FrameDeviationLinear Ball γ e → 0 ≤ e → e ≤ 1 / 4 → FrameTraceRatioLinear Ball γ η → 0 ≤ η →
    s - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH)
      ≤ muDef b' X' cc := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ hG hN hγ hF2 he he4 hF1 hη
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hG
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  exact theoremFSharp K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ g1 g2 g3 g4 g5 g6
    g7 g8 g9 g10 g11 n1 n2 n3 n4 n5 g12 g13 g14 g15 hγ hF2 he he4 hF1 hη

theorem ramification_condition_holds :
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u HH δ Dstar sg η0 η1 e0 de : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    (s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u)
          + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ muDef b' X' cc) ∧
    (s - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u)
          + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ muDef b' X' cc) := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr s u HH δ Dstar sg η0 η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR h0 h0' h1 he0
    hse hde hde4 hcor hS
  obtain ⟨f1, f2, he, -⟩ := ramification_linear_case_holds I (κ ⊕ κ₁) ιf ι Bf Vr γ Dstar sg η0 η1 e0 de hV
    (fun i => (hγ i).le) hD hsg hsg20 hR h0 h0' h1 he0 hse hde hde4 hcor hS
  have hB : Ball = fun i => Bf i * Vr i := funext hBV
  rw [← hB] at f1 f2
  exact ⟨flat_lattice_theorem_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH (2 * e0)
      (5 * sg + 3 * Real.sqrt de) δ hG hN hγ f2 (by positivity) he f1 (by positivity),
    sharp_flat_lattice_theorem_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH (2 * e0)
      (5 * sg + 3 * Real.sqrt de) δ hG hN hγ f2 (by positivity) he f1 (by positivity)⟩

theorem joint_a_ramified_holds : JointARam := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr s u HH δ Dstar sg η0 η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR h0 h0' h1 he0
    hse hde hde4 hcor hS
  exact (ramification_condition_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr s u HH δ Dstar sg η0
    η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR h0 h0' h1 he0 hse hde hde4 hcor hS).1

theorem slope_le_max_slope {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ w, IsUnit (X w).det) (N : Submodule (𝓞 K) V) (hFG : N.FG)
    (hsp : Submodule.span K (N : Set V) = ⊤) (hc : 0 < Fintype.card ι) :
    muDef b X N ≤ muMaxDef b X N := by
  have hne : N ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Submodule K V) = ⊤ := by rw [← hsp]; simp
    have : Subsingleton (Submodule K V) := subsingleton_of_bot_eq_top h0
    have : Subsingleton V := (Submodule.subsingleton_iff K).1 inferInstance
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_zero_of_subsingleton] at this
    omega
  have hLat := (plLat K V ι b X hX N hFG).1
  have := (muChar _ _ _ (Formalism.HermitianLatticesTheory.realize b X) N hLat hne).2.2.2.2
  unfold muDef muMaxDef
  linarith

theorem word_count_bound_holds : WordsR := by
  intro I _ ιf _ Dstar sg C0 Gam hD hsg hC hG hI hd
  have h1 : (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) ≤ RsG ιf := by
    unfold RsG
    calc (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0)
        = ∑ _i : I, Dstar * (Gam ^ 2)⁻¹ / C0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i, (Fintype.card (ιf i) : ℝ) := Finset.sum_le_sum fun i _ => hd i
  have h2 : 0 ≤ Dstar * (Gam ^ 2)⁻¹ / C0 := by positivity
  have h3 : C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) = Dstar / sg := by
    field_simp
  calc Dstar / sg = C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) := h3.symm
    _ ≤ (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) := mul_le_mul_of_nonneg_right hI h2
    _ ≤ RsG ιf := h1

end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice =====
