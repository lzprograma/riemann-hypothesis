module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private alias gram_eq_lemma := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq

private lemma gram_mul_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem dom_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  have hN := FrameDegreeData.upper_of_bor (X := X) hb τ
  have hbd := (hb τ).1
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 hbd
  · have hd := (hx τ).2 i
    have hdiag : ∀ j, mat b τ j j ≠ 0 := by
      intro j
      rw [Matrix.det_of_upperTriangular hN] at hbd
      exact Finset.prod_ne_zero_iff.1 hbd j (Finset.mem_univ j)
    have hP0 : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have heq : dmin X.Gm (rmul x b) τ i = dmin X.Gm x τ i *
        (Complex.normSq (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
          (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) : ℂ) := by
      show lminor (gram τ.1 X.Gm (mat x τ * mat b τ)) i = _
      rw [gram_mul_lemma_2, FrameDegreeData.lminor_conj hN,
        show ∀ z w : ℂ, z * w * conj z = w * (z * conj z) from fun z w => by ring, Complex.mul_conj]
      rfl
    rw [heq, Complex.re_mul_ofReal, ← mul_assoc]
    exact mul_pos hd (Complex.normSq_pos.2 hP0)

theorem stab_mat {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  apply ReciprocityTheory.ChartRestriction.G.AR.Up.KU.herm_mat <;> assumption

theorem gram_gam {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1) = X.Gm.map τ.1 := by
  have h := stab_mat X hγ
  rw [gram_eq_lemma]
  conv_rhs => rw [← h]
  ext a b

  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, emb_cc]

theorem gram_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
  show gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = _
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, gram_gam X hγ τ, gram_eq_lemma]

theorem dom_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  apply ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_dom <;> assumption

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
