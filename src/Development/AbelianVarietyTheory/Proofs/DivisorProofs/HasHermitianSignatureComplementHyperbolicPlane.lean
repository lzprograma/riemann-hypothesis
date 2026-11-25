module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi, Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

end GlobalTheory.LeviTorus
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviUnitary

open Matrix

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, det_neg, det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.LeviUnitary

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.PlaneSig

open Matrix

theorem hasSig_map_conj_of_hasSignature {n r s : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature G r s) : HasSig (G.map (starRingEnd ℂ)) r s := by
  obtain ⟨e, P, hP⟩ := h
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hc
  refine ⟨hc.symm, (P : Matrix _ _ ℂ).submatrix e id, ?_⟩
  have hG : G.map (starRingEnd ℂ) = ((G.map (starRingEnd ℂ)).submatrix e.symm e.symm).submatrix e e := by
    ext i j; simp
  have hL : ((P : Matrix _ _ ℂ).submatrix e id)ᵀ * G.map (starRingEnd ℂ) * ((P : Matrix _ _ ℂ).submatrix e id).map star =
      ((P : Matrix _ _ ℂ)ᵀ * (G.map (starRingEnd ℂ)).submatrix e.symm e.symm * (P : Matrix _ _ ℂ).map star) := by
    conv_lhs => rw [hG, transpose_submatrix, submatrix_mul_equiv, ← Matrix.submatrix_map, submatrix_mul_equiv,
      submatrix_id_id]
  have h3 : (P : Matrix _ _ ℂ)ᵀ * (G.map (starRingEnd ℂ)).submatrix e.symm e.symm * (P : Matrix _ _ ℂ).map star =
      (Formalism.UG.cT (starRingEnd ℂ) (P : Matrix _ _ ℂ) * G.reindex e e * (P : Matrix _ _ ℂ)).map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.mul_apply, map_sum, Formalism.UG.cT]
  rw [hL, h3, hP]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply]

theorem gram_conj {k l : Type} [Fintype k] [Fintype l] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) k ℂ) (B : Matrix (Fin n) l ℂ) :
    Aᴴ * M.map (starRingEnd ℂ) * B = (Aᵀ * M * B.map star).map (starRingEnd ℂ) := by
  ext i j; simp [Matrix.mul_apply, map_sum, Finset.sum_mul]

abbrev colM {n : ℕ} (x : Fin n → ℂ) : Matrix (Fin n) (Fin 1) ℂ := Matrix.of fun i _ => x i

theorem gram_col {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    (colM x)ᵀ * M * (colM y).map star = Matrix.of fun _ _ => x ⬝ᵥ M *ᵥ star y := by
  ext i j
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem gram_col_right {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (ι : Matrix (Fin n) (Fin m) ℂ) (x : Fin n → ℂ) :
    ιᵀ * M * (colM x).map star = Matrix.of fun j _ => (ιᵀ *ᵥ (M *ᵥ star x)) j := by
  ext i j
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem hasSig_complement_plane : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (r s : ℕ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    HasSig M r s → HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  intro n n₁ M X Yv ι P r s hn hM hXX hYY hXY hιX hιY hP hs
  set J := M.map (starRingEnd ℂ) with hJdef
  have hJJ : J.map (starRingEnd ℂ) = M := by ext i j; simp [J]
  have hJ : Jᴴ = J := by
    ext i j
    have := congrFun (congrFun hM i) j
    simp [conjTranspose_apply] at this
    simp [J, conjTranspose_apply, ← this]
  have hJs : Formalism.UG.HasSignature J r s := GlobalTheory.FunObj.hasSignature_of_hasSig_conj (by rw [hJJ]; exact hs)
  set T := colM X
  set T' := colM Yv
  have h1 : Tᴴ * J * T = 0 := by
    rw [gram_conj, gram_col, hXX]; ext i j; simp
  have h2 : T'ᴴ * J * T' = 0 := by
    rw [gram_conj, gram_col, hYY]; ext i j; simp
  have h3 : Tᴴ * J * T' = 1 := by
    rw [gram_conj, gram_col, hXY]; ext i j; fin_cases i; fin_cases j; simp
  have h4' : ιᴴ * J * T = 0 := by
    rw [gram_conj, gram_col_right, hιX]; ext i j; simp
  have h5' : ιᴴ * J * T' = 0 := by
    rw [gram_conj, gram_col_right, hιY]; ext i j; simp
  have h4 : Tᴴ * J * ι = 0 := by rw [GlobalTheory.AdaptedExists.gram_swap hJ, h4', conjTranspose_zero]
  have h5 : T'ᴴ * J * ι = 0 := by rw [GlobalTheory.AdaptedExists.gram_swap hJ, h5', conjTranspose_zero]
  have h3' : T'ᴴ * J * T = 1 := by rw [GlobalTheory.AdaptedExists.gram_swap hJ, h3, conjTranspose_one]
  have hGι : ιᴴ * J * ι = (ιᵀ * M * ι.map star).map (starRingEnd ℂ) := gram_conj M ι ι

  set Q : Matrix (Fin n) ((Fin 1 ⊕ Fin 1) ⊕ Fin n₁) ℂ := fromCols (fromCols T T') ι with hQ
  set L : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin n₁) (Fin n) ℂ :=
    fromRows (fromRows (T'ᴴ * J) (Tᴴ * J)) (P * (1 - T * (T'ᴴ * J) - T' * (Tᴴ * J))) with hL
  have hLQ : L * Q = 1 := by
    rw [Matrix.mul_assoc] at h1 h2 h3 h4 h5 h3'
    simp only [hL, hQ, fromRows_mul, mul_fromCols, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, h2, h3, h4, h5, h3', hP, Matrix.mul_zero, sub_zero, sub_self]
    ext ((a | a) | a) ((b | b) | b) <;> simp [Matrix.one_apply]
  obtain ⟨f⟩ : Nonempty (Fin n ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n₁) := Fintype.card_eq.1 (by simp; omega)
  set Q' : Matrix (Fin n) (Fin n) ℂ := Q.submatrix id f with hQ'
  have hLQ' : L.submatrix f id * Q' = 1 := by
    have := Matrix.submatrix_mul_equiv L Q f (Equiv.refl (Fin n)) f
    rw [hLQ, submatrix_one_equiv] at this
    exact this
  have hdQ : Matrix.det Q' ≠ (0 : ℂ) := Matrix.det_ne_zero_of_left_inverse hLQ'
  have hdM : M.det ≠ 0 := GlobalTheory.LeviUnitary.det_ne_zero_of_hasSig hs
  have hdJ : J.det ≠ 0 := by
    rw [hJdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hdM
  have hQJQ : Qᴴ * J * Q = fromBlocks (fromBlocks 0 1 1 0) 0 0 (ιᴴ * J * ι) := by
    rw [Matrix.mul_assoc] at h1 h2 h3 h4 h5 h3' h4' h5'
    simp only [hQ, conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc, mul_fromCols, fromRows_mul,
      h1, h2, h3, h4, h5, h3', h4', h5']
    ext ((a | a) | a) ((b | b) | b) <;> simp
  have h6 : (ιᴴ * J * ι).det ≠ 0 := by
    have h7 : (Q'ᴴ * J * Q').det ≠ 0 := by
      rw [det_mul, det_mul, det_conjTranspose]
      exact mul_ne_zero (mul_ne_zero (by simpa using hdQ) hdJ) hdQ
    have h8 : Q'ᴴ * J * Q' = (Qᴴ * J * Q).submatrix f f := by
      ext i j; simp [Q', Matrix.mul_apply]
    have : (Qᴴ * J * Q).det ≠ 0 := by rwa [h8, det_submatrix_equiv_self] at h7
    rw [hQJQ, det_fromBlocks_zero₂₁] at this
    exact right_ne_zero_of_mul this
  have hc := GlobalTheory.AdaptedExists.hasSignature_complement n n₁ r s (Fin 1) J T T' ι hJ hJs (by simp; omega)
    h1 h2 h3 h4 h5 h6
  simp only [Fintype.card_fin] at hc
  have := hasSig_map_conj_of_hasSignature hc
  rwa [hGι, Matrix.map_map, show (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id from funext fun z => Complex.conj_conj z,
    Matrix.map_id] at this

end GlobalTheory.PlaneSig
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane =====
