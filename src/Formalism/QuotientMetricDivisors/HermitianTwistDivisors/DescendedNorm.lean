module

public import Formalism.QuotientMetricDivisors.HeightBoundExactNorms
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean

@[expose] public section

open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

namespace OperatorNormFrames

theorem cnorm_eq {n : ℕ} (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n))‖ :=
  Formalism.HN.PlaceOperatorNorms.cnorm_eq u

theorem cnorm_nonneg {n : ℕ} (u : Fin n → ℂ) : 0 ≤ Formalism.HermitianLatticesTheory.cnorm u :=
  Real.sqrt_nonneg _

theorem cnorm_star {n : ℕ} (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (star u) =
      Formalism.HermitianLatticesTheory.cnorm u := by simp [Formalism.HermitianLatticesTheory.cnorm]

theorem norm_dot_le {n : ℕ} (y w : Fin n → ℂ) :
    ‖y ⬝ᵥ w‖ ≤ Formalism.HermitianLatticesTheory.cnorm y *
      Formalism.HermitianLatticesTheory.cnorm w := by
  refine LE.le.trans ?_ (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
  simpa [dotProduct, norm_mul] using norm_sum_le Finset.univ fun i => y i * w i

theorem star_dot_self {n : ℕ} (w : Fin n → ℂ) :
    star w ⬝ᵥ w = ((Formalism.HermitianLatticesTheory.cnorm w ^ 2 : ℝ) : ℂ) := by
  rw [Formalism.HermitianLatticesTheory.cnorm,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  push_cast; simp only [dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => Complex.conj_mul' (w i)

theorem opNorm_le_iff {a D : ℕ} (A : Matrix (Fin D) (Fin a) ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ ≤ c ↔
      ∀ (x : Fin a → ℂ) (y : Fin D → ℂ), ‖y ⬝ᵥ A.mulVec x‖ ≤
        c * Formalism.HermitianLatticesTheory.cnorm x *
          Formalism.HermitianLatticesTheory.cnorm y := by
  have hT (x : Fin a → ℂ) :
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) (WithLp.toLp 2 x)‖ =
        Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) := by
    simp [cnorm_eq, Matrix.toLpLin_apply]
  refine ⟨fun h x y => ?_, fun h => ContinuousLinearMap.opNorm_le_bound _ hc fun z => ?_⟩
  · have h2 : Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) ≤
        c * Formalism.HermitianLatticesTheory.cnorm x := by
      rw [← hT, cnorm_eq x]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    exact (norm_dot_le _ _).trans
      ((mul_le_mul_of_nonneg_left h2 (cnorm_nonneg y)).trans_eq (by ring))
  · obtain ⟨x, rfl⟩ : ∃ x, z = WithLp.toLp 2 x := ⟨z.ofLp, by simp⟩
    rw [hT, ← cnorm_eq]
    have h3 := h x (star (A.mulVec x))
    rw [star_dot_self, cnorm_star, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h3
    rcases (cnorm_nonneg (A.mulVec x)).eq_or_lt with h0 | hpos
    · exact h0 ▸ mul_nonneg hc (cnorm_nonneg _)
    · exact le_of_mul_le_mul_right (by simpa [sq] using h3) hpos

def pmat {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) : Matrix (Fin D) (Fin a) ℂ :=
  Matrix.of fun k i => v.embedding (B (Pi.single i 1) (Pi.single k 1))

theorem pairC_eq {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    pairC v B x y = y ⬝ᵥ (pmat v B).mulVec x := by
  simp only [pairC, pmat, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem toMatrix_dual {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) :
    (LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin D)).dualBasis B).map
        v.embedding = pmat v B := by ext k i; simp [pmat, LinearMap.toMatrix_apply]

theorem dot_frames {a D : ℕ} (Y : Matrix (Fin D) (Fin D) ℂ) (M : Matrix (Fin D) (Fin a) ℂ)
    (X : Matrix (Fin a) (Fin a) ℂ) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    y ⬝ᵥ (Yᵀ * M * X).mulVec x = (Y.mulVec y) ⬝ᵥ M.mulVec (X.mulVec x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem opNormAt_dual_eq {K : Type} [Field K] [NumberField K] [StarRing K] {a D : ℕ}
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hE : ∀ v, IsUnit (XE v).det)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (v : InfinitePlace K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
        (Formalism.HN.dualFrame XE) v B =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((XE v)ᵀ * pmat v B * XM v))‖ := by
  simp only [Formalism.HN.opNormAt, Formalism.HN.dualFrame]
  rw [toMatrix_dual, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.det_transpose (XE v)).symm ▸ hE v)]

theorem mul_inv_mulVec {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det)
    (x : Fin n → ℂ) : Y.mulVec (Y⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hY, Matrix.one_mulVec]

theorem inv_mul_mulVec {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det)
    (x : Fin n → ℂ) : Y⁻¹.mulVec (Y.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hY, Matrix.one_mulVec]

end OperatorNormFrames

open OperatorNormFrames

theorem frobenius_norm_rational : FnormRat := fun K _ _ _ n X v x y => by
  have hv (z : Fin n → K) : (fun i => v.embedding (z i)) =
      Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v z := by
    ext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  exact ⟨by simp [fnorm, Formalism.HermitianLatticesTheory.normAt,
      Formalism.HermitianLatticesTheory.fcoord, hv],
    by simp [fmaj, Formalism.HermitianLatticesTheory.majAt,
      Formalism.HermitianLatticesTheory.fcoord, hv],
    (star_dot_self _).symm⟩

theorem operator_norm_dual : OpNormDual := fun K _ _ _ a D XM XE hM hE B v c hc => by
  rw [opNormAt_dual_eq XM XE hE B v, opNorm_le_iff _ c hc]
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩
  · simpa only [fnorm, pairC_eq, dot_frames, mul_inv_mulVec _ (hE v),
      mul_inv_mulVec _ (hM v)] using h ((XM v)⁻¹.mulVec x) ((XE v)⁻¹.mulVec y)
  · simpa only [pairC_eq, fnorm, inv_mul_mulVec _ (hM v), inv_mul_mulVec _ (hE v),
      ← dot_frames] using h ((XM v).mulVec x) ((XE v).mulVec y)

namespace OperatorNormFrames

theorem filter_succ {m : ℕ} (j : Fin m) :
    Finset.univ.filter (fun i : Fin m => i.castSucc < j.succ) =
      insert j (Finset.univ.filter (fun i : Fin m => i.castSucc < j.castSucc)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

theorem prod_filter_succ {m : ℕ} (k : Fin m → ℝ) (j : Fin m) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.succ), k i =
      k j * ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.castSucc), k i := by
  rw [filter_succ, Finset.prod_insert (by simp)]

theorem filter_last {m : ℕ} :
    Finset.univ.filter (fun i : Fin m => i.castSucc < Fin.last m) = Finset.univ :=
  Finset.filter_true_of_mem fun i _ => Fin.castSucc_lt_last i

theorem filter_zero {m : ℕ} :
    Finset.univ.filter (fun i : Fin m => i.castSucc < (0 : Fin (m + 1))) = ∅ :=
  Finset.filter_false_of_mem fun _ _ => Fin.not_lt_zero _

theorem minOver_le {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (p : Ix) :
    minOver f ≤ f p := Finset.inf'_le _ (Finset.mem_univ p)

theorem exists_minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) :
    ∃ p, minOver f = f p :=
  let ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f; ⟨i, hi⟩

theorem le_minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (a : ℝ)
    (h : ∀ p, a ≤ f p) : a ≤ minOver f := Finset.le_inf' Finset.univ_nonempty _ fun p _ => h p

theorem cnorm_sq_mulVec {n d : ℕ} (Z : Matrix (Fin d) (Fin n) ℂ) (y : Fin n → ℂ) :
    ((Formalism.HermitianLatticesTheory.cnorm (Z.mulVec y) ^ 2 : ℝ) : ℂ) =
      star y ⬝ᵥ (Zᴴ * Z).mulVec y := by
  rw [← star_dot_self, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem quot_rep {n D : ℕ} (Hc X0 : Matrix (Fin n) (Fin n) ℂ) (h0 : IsUnit X0.det)
    (hH : (X0⁻¹)ᴴ * X0⁻¹ = Hc) (Pc : Matrix (Fin D) (Fin n) ℂ) (XQ : Matrix (Fin D) (Fin D) ℂ)
    (hQ : IsUnit XQ.det) (hG : (XQ⁻¹)ᴴ * XQ⁻¹ = (Pc * Hc⁻¹ * Pcᴴ)⁻¹) (y : Fin D → ℂ) :
    ∃ x : Fin n → ℂ, Pc.mulVec x = y ∧ fnorm X0 x = fnorm XQ y ∧
      ∀ u : Fin n → ℂ, Pc.mulVec u = 0 → fmaj X0 x u = 0 := by
  generalize hM : Pc * Hc⁻¹ * Pcᴴ = M at hG
  have hHcU : IsUnit Hc.det := by
    rw [← hH, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (Matrix.isUnit_nonsing_inv_det X0 h0).star.mul (Matrix.isUnit_nonsing_inv_det X0 h0)
  have hMU : IsUnit M.det := Matrix.isUnit_nonsing_inv_det_iff.mp <| by
    rw [← hG, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (Matrix.isUnit_nonsing_inv_det XQ hQ).star.mul (Matrix.isUnit_nonsing_inv_det XQ hQ)
  have hHiH : (Hc⁻¹)ᴴ = Hc⁻¹ := by simp [Matrix.conjTranspose_nonsing_inv, ← hH]
  have hGH : (M⁻¹)ᴴ = M⁻¹ := by simp [← hG]
  have hA : (X0⁻¹ * (Hc⁻¹ * Pcᴴ * M⁻¹))ᴴ * X0⁻¹ = M⁻¹ * Pc := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hH, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHiH, hGH]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHcU, Matrix.mul_one]
  refine ⟨(Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y, ?_, ?_, fun u hu => ?_⟩
  · rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM,
      Matrix.mul_nonsing_inv _ hMU, Matrix.one_mulVec]
  · refine (sq_eq_sq₀ (cnorm_nonneg _) (cnorm_nonneg _)).mp <| Complex.ofReal_injective ?_
    rw [Matrix.mulVec_mulVec, cnorm_sq_mulVec, cnorm_sq_mulVec,
      ← Matrix.mul_assoc _ _ (Hc⁻¹ * Pcᴴ * M⁻¹), hA]
    exact congrArg (fun Z => star y ⬝ᵥ Z *ᵥ y) ((by simp only [Matrix.mul_assoc] :
      M⁻¹ * Pc * (Hc⁻¹ * Pcᴴ * M⁻¹) = M⁻¹ * (Pc * Hc⁻¹ * Pcᴴ) * M⁻¹).trans
      (by rw [hM, Matrix.nonsing_inv_mul _ hMU, Matrix.one_mul, hG]))
  · show star (X0⁻¹ *ᵥ ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y)) ⬝ᵥ (X0⁻¹ *ᵥ u) = 0
    rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hA, ← Matrix.mulVec_mulVec, hu]; simp

theorem dual_expand {K : Type} [Field K] {D : ℕ} (f : Module.Dual K (Fin D → K)) (e : Fin D → K) :
    f e = ∑ d, e d * f (Pi.single d 1) := by
  conv_lhs =>
    rw [show e = ∑ d, e d • Pi.single d 1 by ext; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum]

theorem map_expand {K : Type} [Field K] {a D : ℕ}
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (φ : Fin a → K) (e : Fin D → K) :
    B φ e = ∑ i, φ i * B (Pi.single i 1) e := by
  conv_lhs =>
    rw [show φ = ∑ i, φ i • Pi.single i 1 by ext; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, LinearMap.sum_apply]

theorem pairC_transfer {K : Type} [Field K] [NumberField K] {a b n D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (A : (Fin b → K) →ₗ[K] Module.Dual K (Fin n → K))
    (N : Matrix (Fin D) (Fin n) K) (C : Matrix (Fin b) (Fin a) K)
    (h : ∀ φ F, B φ (N.mulVec F) = A (C.mulVec φ) F) (x : Fin a → ℂ) (F : Fin n → ℂ) :
    pairC v B x ((N.map v.embedding).mulVec F) = pairC v A ((C.map v.embedding).mulVec x) F := by
  have hM : (N.map v.embedding)ᵀ * pmat v B = pmat v A * C.map v.embedding := by
    ext l i
    have h1 := h (Pi.single i 1) (Pi.single l 1)
    rw [dual_expand (B (Pi.single i 1)), map_expand A] at h1
    simpa [Matrix.mul_apply, pmat, Matrix.mulVec_single_one, mul_comm] using
      congrArg v.embedding h1
  rw [pairC_eq, pairC_eq, Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem opNormAt_nonneg {K : Type} [Field K] [NumberField K] [StarRing K]
    {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (φ : V →ₗ[K] W) :
    0 ≤ Formalism.HN.opNormAt b X b' X' v φ := norm_nonneg _

def nrm {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

theorem nrm_mul_le {a b c : ℕ} (A : Matrix (Fin c) (Fin b) ℂ) (B : Matrix (Fin b) (Fin a) ℂ) :
    nrm (A * B) ≤ nrm A * nrm B := by
  simpa only [nrm, show LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A * B)) =
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).comp
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)) by
    ext; simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]] using
    ContinuousLinearMap.opNorm_comp_le _ _

theorem opNormAt_mulVecLin {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
    (v : InfinitePlace K) (N : Matrix (Fin b) (Fin a) K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) X (Pi.basisFun K (Fin b)) X' v
        (Matrix.mulVecLin N) = nrm ((X' v)⁻¹ * N.map v.embedding * X v) := by
  simp only [Formalism.HN.opNormAt, nrm,
    show LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) (Matrix.mulVecLin N) =
      N by ext; simp]

theorem mulVecLin_ne_zero {K : Type} [Field K] {a b : ℕ} (N : Matrix (Fin b) (Fin a) K)
    (h : N ≠ 0) : Matrix.mulVecLin N ≠ 0 := fun h0 =>
  h <| Matrix.ext fun i j => by simpa using congrArg (fun f => f (Pi.single j 1) i) h0

section G
variable {K : Type} [Field K] [NumberField K] {D : ℕ}
theorem map_mulVec_emb {n : ℕ} (v : InfinitePlace K) (N : Matrix (Fin D) (Fin n) K)
    (x : Fin n → K) : (fun i => v.embedding (N.mulVec x i)) =
      (N.map v.embedding).mulVec fun i => v.embedding (x i) := by
  ext i; simp [Matrix.mulVec, dotProduct]
end G

theorem place_bound {K : Type} [Field K] [NumberField K] [StarRing K] {n D a b : ℕ}
    (Xa : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (ha : ∀ v, IsUnit (Xa v).det)
    (Xb : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (hb : ∀ v, IsUnit (Xb v).det)
    (col : Matrix (Fin b) (Fin a) K)
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin D) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hQ : IsQuotMetric P H XQ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hE : ∀ v, IsUnit (XE v).det)
    (ι : Matrix (Fin D) (Fin D) K) (hι : IsUnit ι.det)
    {Ix : Type} [Fintype Ix] (Qp : Ix → Submodule K (Fin D → K)) (hsup : (⨆ p, Qp p) = ⊤)
    (v : InfinitePlace K) (s : Ix → ℝ) (smin : ℝ) (hsmin : 0 < smin) (hs : ∀ p, smin ≤ s p)
    (hspec : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x)
        (ι.mulVec y) =
        ((s p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y)
    (Pt : (Fin b → K) →ₗ[K] Module.Dual K (Fin n → K))
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (hB : ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt (col.mulVec φ) F)
    (p k : ℝ)
    (hp : Formalism.HN.opNormAt (Pi.basisFun K (Fin b)) Xb (Pi.basisFun K (Fin n)).dualBasis
      (Formalism.HN.dualFrame X0) v Pt ≤ p)
    (hk : Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin b)) Xb v
      (Matrix.mulVecLin col) ≤ k) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin D)).dualBasis
      (Formalism.HN.dualFrame XE) v B ≤ p * k / Real.sqrt smin := by
  let _ := hP
  have hp0 : 0 ≤ p := (opNormAt_nonneg _ _ _ _ _ _).trans hp
  have hr : 0 < Real.sqrt smin := Real.sqrt_pos.2 hsmin
  let ι' : Matrix (Fin D) (Fin D) ℂ := ι.map v.embedding
  let GQ : Matrix (Fin D) (Fin D) ℂ := ((XQ v)⁻¹)ᴴ * (XQ v)⁻¹
  let A : Matrix (Fin D) (Fin D) ℂ := ι'ᴴ * (((XE v)⁻¹)ᴴ * (XE v)⁻¹) * ι'
  have hι'U : IsUnit ι'.det := by
    simpa [ι', ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero] using
      isUnit_iff_ne_zero.mp hι
  have hGQH : GQᴴ = GQ := by simp [GQ]
  have hAH : Aᴴ = A := by simp [A, Matrix.mul_assoc]
  have hsj (j : Fin D) :
      (fun i => v.embedding ((Pi.single j (1 : K) : Fin D → K) i)) = Pi.single j 1 := by
    ext i; rcases eq_or_ne i j with rfl | h <;> simp [*]
  have heig (q : Ix) (x : Fin D → K) (hx : x ∈ Qp q) :
      A *ᵥ (fun i => v.embedding (x i)) = (s q : ℂ) • (GQ *ᵥ fun i => v.embedding (x i)) := by
    suffices star (fun i => v.embedding (x i)) ᵥ* A =
        (s q : ℂ) • (star (fun i => v.embedding (x i)) ᵥ* GQ) by
      simpa [Matrix.star_vecMul, hAH, hGQH] using congrArg star this
    ext j
    have h1 := hspec q x hx (Pi.single j 1)
    have hfm (Y : Matrix (Fin D) (Fin D) ℂ) (a' b' : Fin D → ℂ) :
        fmaj Y a' b' = star a' ⬝ᵥ ((Y⁻¹)ᴴ * Y⁻¹) *ᵥ b' := by
      show star (Y⁻¹ *ᵥ a') ⬝ᵥ (Y⁻¹ *ᵥ b') = _
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [← (frobenius_norm_rational K D XE v (ι *ᵥ x) (ι *ᵥ Pi.single j 1)).2.1,
      ← (frobenius_norm_rational K D XQ v x (Pi.single j 1)).2.1, hfm, hfm,
      map_mulVec_emb, map_mulVec_emb, hsj, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h1
    simpa [A, GQ, ι', Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul, dotProduct,
      Pi.single_apply] using h1
  have hdec (i : Fin D) :
      ∃ f : Ix → Fin D → K, (∀ q, f q ∈ Qp q) ∧ ∑ q, f q = Pi.single i 1 := by
    classical
    refine Submodule.iSup_induction Qp
      (motive := fun z => ∃ f : Ix → Fin D → K, (∀ q, f q ∈ Qp q) ∧ ∑ q, f q = z)
      (hsup ▸ Submodule.mem_top) (fun q x hx => ⟨Pi.single q x, fun r => ?_, by simp⟩)
      ⟨0, fun _ => zero_mem _, by simp⟩ ?_
    · rcases eq_or_ne r q with rfl | h <;> simp [*, zero_mem]
    · rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, fun q => add_mem (hf q) (hg q), by simp [Finset.sum_add_distrib]⟩
  have SPEC (w : Fin D → ℂ) : smin * fnorm (XQ v) w ^ 2 ≤ fnorm (XE v) (ι' *ᵥ w) ^ 2 := by
    choose f hf hfs using hdec
    let W (q : Ix) : Fin D → ℂ := ∑ i, w i • fun j => v.embedding (f i q j)
    have hWsum : ∑ q, W q = w := by
      ext j; simp only [W, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; rw [Finset.sum_comm]
      have hj (i : Fin D) : ∑ q, v.embedding (f i q j) = (Pi.single i 1 : Fin D → ℂ) j := by
        rw [← map_sum, ← Finset.sum_apply, hfs i]; exact congrFun (hsj i) j
      simp [← Finset.mul_sum, hj, Pi.single_apply]
    have hWe (q : Ix) : A *ᵥ W q = (s q : ℂ) • (GQ *ᵥ W q) := by
      simp only [W, Matrix.mulVec_sum, Matrix.mulVec_smul, heig _ _ (hf _ q), Finset.smul_sum]
      exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _
    let z : Fin D → ℂ := ∑ q, (Real.sqrt (s q - smin) : ℂ) • W q
    have hkey : ((fnorm (XE v) (ι' *ᵥ w) ^ 2 : ℝ) : ℂ) - (smin : ℂ) * (fnorm (XQ v) w ^ 2 : ℝ) =
        (fnorm (XQ v) z ^ 2 : ℝ) := by
      have hfE : ((fnorm (XE v) (ι' *ᵥ w) ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ A *ᵥ w := by
        simpa [fnorm, A, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
          cnorm_sq_mulVec ((XE v)⁻¹ * ι') w
      rw [hfE]; simp only [fnorm, cnorm_sq_mulVec]
      change star w ⬝ᵥ A *ᵥ w - (smin : ℂ) * (star w ⬝ᵥ GQ *ᵥ w) = star z ⬝ᵥ GQ *ᵥ z
      rw [← hWsum]
      simp only [z, star_sum, sum_dotProduct, Matrix.mulVec_sum, dotProduct_sum, hWe,
        Matrix.mulVec_smul, star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
      by_cases hqr : s r = s q
      · rw [hqr, ← sub_mul, ← Complex.ofReal_sub, ← mul_assoc, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (sub_nonneg.mpr (hs q))]
      · have h0 : star (W r) ⬝ᵥ GQ *ᵥ W q = 0 := by
          refine (mul_eq_zero.mp ?_).resolve_left
            (sub_ne_zero.mpr <| mt Complex.ofReal_inj.mp hqr)
          calc ((s r : ℂ) - s q) * (star (W r) ⬝ᵥ GQ *ᵥ W q)
              = star (A *ᵥ W r) ⬝ᵥ W q - star (W r) ⬝ᵥ A *ᵥ W q := by
                rw [sub_mul, hWe r, hWe q, star_smul, Complex.star_def, Complex.conj_ofReal,
                  smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Matrix.star_mulVec,
                  hGQH, Matrix.dotProduct_mulVec]
            _ = 0 := by rw [Matrix.star_mulVec, hAH, Matrix.dotProduct_mulVec, sub_self]
        simp [h0]
    exact sub_nonneg.mp ((show _ = fnorm (XQ v) z ^ 2 from mod_cast hkey).symm ▸ sq_nonneg _)
  have hk0 : 0 ≤ k := (opNormAt_nonneg _ _ _ _ _ _).trans hk
  rw [operator_norm_dual K a D Xa XE ha hE B v _ (div_nonneg (mul_nonneg hp0 hk0) hr.le)]
  intro x y
  obtain ⟨F, hF, hFn, -⟩ := quot_rep (H.map v.embedding) (X0 v) (h0 v).1 (h0 v).2
    (P.map v.embedding) (XQ v) (hQ v).1 (hQ v).2 (ι'⁻¹ *ᵥ y)
  conv_lhs =>
    rw [show y = ((ι * P).map v.embedding) *ᵥ F by
        rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hF, mul_inv_mulVec _ hι'U],
      pairC_transfer v B Pt (ι * P) col (fun φ F' => by rw [← Matrix.mulVec_mulVec]; exact hB φ F')]
  have h4 : fnorm (Xb v) ((col.map v.embedding) *ᵥ x) ≤ k * fnorm (Xa v) x := by
    let M := (Xb v)⁻¹ * col.map v.embedding * Xa v
    have hnk : nrm M ≤ k := by simpa [M, opNormAt_mulVecLin] using hk
    have e : (Xb v)⁻¹ *ᵥ ((col.map v.embedding) *ᵥ x) = M *ᵥ ((Xa v)⁻¹ *ᵥ x) := by
      simp only [M, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ (ha v)]
    have h1 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm
      (WithLp.toLp 2 ((Xa v)⁻¹ *ᵥ x))
    rw [fnorm, fnorm, e, cnorm_eq, cnorm_eq ((Xa v)⁻¹ *ᵥ x)]
    refine LE.le.trans ?_ (mul_le_mul_of_nonneg_right hnk (norm_nonneg _))
    simpa [nrm, Matrix.toLpLin_apply] using h1
  have h5 : fnorm (X0 v) F ≤ fnorm (XE v) y / Real.sqrt smin := by
    rw [hFn, le_div_iff₀ hr, mul_comm]
    have hs1 := Real.sqrt_le_sqrt (SPEC (ι'⁻¹ *ᵥ y))
    unfold fnorm at hs1 ⊢
    rwa [mul_inv_mulVec _ hι'U, Real.sqrt_mul hsmin.le, Real.sqrt_sq (cnorm_nonneg _),
      Real.sqrt_sq (cnorm_nonneg _)] at hs1
  exact ((operator_norm_dual K b n Xb X0 hb (fun v => (h0 v).1) Pt v p hp0).mp hp
    ((col.map v.embedding) *ᵥ x) F).trans ((mul_le_mul (mul_le_mul_of_nonneg_left h4 hp0) h5
      (cnorm_nonneg _) (mul_nonneg hp0 (mul_nonneg hk0 (cnorm_nonneg _)))).trans_eq (by ring))

end OperatorNormFrames

theorem successive_minimum_log : SminLog := fun Ix J _ _ _ κ lam hκ hlam => by
  have hpos (p : Ix) : 0 < ∏ j, lam j p := Finset.prod_pos fun j _ => hlam j p
  have hlog (p : Ix) : Real.log (∏ j, lam j p) = ∑ j, Real.log (lam j p) :=
    Real.log_prod fun j _ => (hlam j p).ne'
  obtain ⟨q, hq⟩ := exists_minOver fun p => ∏ j, lam j p
  refine ⟨hq ▸ mul_pos hκ (hpos q), fun p => mul_le_mul_of_nonneg_left (minOver_le _ p) hκ.le,
    ⟨q, by rw [hq]⟩, ?_⟩
  rw [hq, Real.log_mul hκ.ne' (hpos q).ne', hlog q]
  refine congrArg (Real.log κ + ·) (le_antisymm (le_minOver _ _ fun p => ?_) (minOver_le _ q))
  rw [← hlog q, ← hlog p]; exact Real.log_le_log (hpos q) (hq ▸ minOver_le _ p)

theorem composition_norm_at_place : CompNormAt := fun K _ _ _ m c Xc hX Kj => by
  have key (v : InfinitePlace K) : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
      ∏ j : Fin m, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) := by
    suffices ∀ i : Fin (m + 1), nrm ((Xc i v)⁻¹ * (chainMat Kj i).map v.embedding * Xc 0 v) ≤
        ∏ j ∈ Finset.univ.filter (fun j : Fin m => j.castSucc < i),
          nrm ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v) by
      simpa [opNormAt_mulVecLin, filter_last] using this (Fin.last m)
    intro i; induction i using Fin.induction with
    | zero =>
      rw [filter_zero, Finset.prod_empty]
      change nrm ((Xc 0 v)⁻¹ * (1 : Matrix _ _ K).map v.embedding * Xc 0 v) ≤ 1
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        Matrix.nonsing_inv_mul _ (hX 0 v)]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun _ => by simp
    | succ j ih =>
      rw [prod_filter_succ]
      have h2 : (Xc j.succ v)⁻¹ * (chainMat Kj j.succ).map v.embedding * Xc 0 v =
          ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v) *
            ((Xc j.castSucc v)⁻¹ * (chainMat Kj j.castSucc).map v.embedding * Xc 0 v) := by
        change (Xc j.succ v)⁻¹ * (Kj j * chainMat Kj j.castSucc).map v.embedding * Xc 0 v = _
        rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (Xc j.castSucc v), Matrix.mul_nonsing_inv _ (hX _ v), Matrix.one_mul]
      rw [h2]; exact (nrm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
  refine ⟨key, fun hne => ?_⟩
  simp only [Formalism.HN.htMap]; rw [← Finset.mul_sum, Finset.sum_comm]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (by positivity)
  have hpos := Formalism.HN.PlaceOperatorNorms.opNormAt_pos
    (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
    (hX _) (hX _) v _ (mulVecLin_ne_zero _ hne)
  have hprod := hpos.trans_le (key v)
  rw [← Real.log_prod fun j hj => pow_ne_zero 2 (Finset.prod_ne_zero_iff.mp hprod.ne' j hj),
    Finset.prod_pow]
  exact Real.log_le_log (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le (key v) 2)

theorem height_constant_first : HeightBoundConstant := by
  intro K _ _ _ n D m c Xc hXc Kj H X0 h0 P hP XQ hQ XE hE ι hι Ix J _ _ _ Qp hsup κ lam lamL
    hκ hlamL hle hspec Pt B hB hB0 pU kU hpU hkU
  have hk (v : InfinitePlace K) : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤ ∏ j, kU j v :=
    ((composition_norm_at_place K m c Xc hXc Kj).1 v).trans
      (Finset.prod_le_prod₀ (fun _ _ => opNormAt_nonneg _ _ _ _ _ _) fun j _ => hkU j v)
  have hlogv (v : InfinitePlace K) :
      Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
        Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
          minOver (fun p => ∑ j, Real.log (lamL j p v)) := by
    obtain ⟨S1, S2, -, S4⟩ :=
      successive_minimum_log Ix J (κ v) (fun j p => lamL j p v) (hκ v) fun j p => hlamL j p v
    have hs (p : Ix) : κ v * minOver (fun p => ∏ j, lamL j p v) ≤ κ v * ∏ j, lam j p v :=
      (S2 p).trans <| mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun j _ => (hlamL j p v).le) fun j _ => hle j p v) (hκ v).le
    have hpl := place_bound (Xc 0) (hXc 0) (Xc (Fin.last m)) (hXc (Fin.last m))
      (chainMat Kj (Fin.last m)) H X0 h0 P hP XQ hQ XE hE ι hι Qp hsup v
      (fun p => κ v * ∏ j, lam j p v) (κ v * minOver (fun p => ∏ j, lamL j p v)) S1 hs
      (fun p x hx y => hspec v p x hx y) Pt B hB (pU v) (∏ j, kU j v) (hpU v) (hk v)
    have hpos := Formalism.HN.PlaceOperatorNorms.opNormAt_pos
      (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin D)).dualBasis
      (Formalism.HN.dualFrame XE) (hXc 0)
      (fun w => Matrix.isUnit_nonsing_inv_det _ ((Matrix.det_transpose (XE w)).symm ▸ hE w)) v B hB0
    have hnum : 0 < pU v * ∏ j, kU j v :=
      (div_pos_iff_of_pos_right (Real.sqrt_pos.2 S1)).mp (hpos.trans_le hpl)
    have hprod : 0 < ∏ j, kU j v :=
      pos_of_mul_pos_right hnum ((opNormAt_nonneg _ _ _ _ _ _).trans (hpU v))
    have hpUpos : 0 < pU v := pos_of_mul_pos_left hnum
      (Finset.prod_nonneg fun j _ => (opNormAt_nonneg _ _ _ _ _ _).trans (hkU j v))
    have hprod2 : 0 < ∏ j, kU j v ^ 2 := Finset.prod_pow Finset.univ 2 (kU · v) ▸ pow_pos hprod 2
    rw [sub_sub, ← S4,
      ← Real.log_prod fun j hj => pow_ne_zero 2 (Finset.prod_ne_zero_iff.mp hprod.ne' j hj),
      ← Real.log_mul (pow_pos hpUpos 2).ne' hprod2.ne',
      ← Real.log_div (mul_pos (pow_pos hpUpos 2) hprod2).ne' S1.ne']
    refine Real.log_le_log (pow_pos hpos 2) ?_
    rw [Finset.prod_pow, ← mul_pow, ← Real.sq_sqrt S1.le, ← div_pow]
    exact pow_le_pow_left₀ hpos.le hpl 2
  refine ⟨hlogv, ?_⟩
  unfold Formalism.HN.htMap meanLog
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hlogv v)
    (by positivity)).trans_eq ?_
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring

end Formalism.DivisionValues
