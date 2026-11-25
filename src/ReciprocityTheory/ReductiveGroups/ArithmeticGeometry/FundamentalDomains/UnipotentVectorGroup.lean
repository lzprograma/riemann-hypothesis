module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem hermC_emb_emb_eq_zero_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (τ : E →+* ℂ) (i k : Fin 2) :
    hermC τ X.Gm (Data.emb τ (u i)) (Data.emb τ (u k)) = 0 := by
  have h := congrArg τ (hiso.1 i k)

  simp only [herm, map_sum, map_mul, map_zero, _root_.ReciprocityTheory.ChartRestriction.G.FD.emb_cc] at h
  simp only [hermC, Data.emb]
  exact h

private theorem zmat_mulVec_eq {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (w : Fin r → ℂ) :
    Matrix.mulVec (X.zmat u b τ) w = fun p => w p - ∑ i, (Complex.I * (X.c τ : ℂ) *
      ∑ k, b τ i k * hermC τ.1 X.Gm w (Data.emb τ.1 (u k))) * Data.emb τ.1 (u i) p := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Data.zmat, Matrix.of_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  congr 1
  simp only [hermC, Fin.sum_univ_two, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem hermC_sub_sum_smul_expand {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (w w' : Fin r → ℂ)
    (v : Fin 2 → Fin r → ℂ) (α β : Fin 2 → ℂ) :
    hermC τ G (fun p => w p - ∑ i, α i * v i p) (fun p => w' p - ∑ i, β i * v i p) =
      hermC τ G w w' - ∑ i, starRingEnd ℂ (β i) * hermC τ G w (v i) -
        ∑ i, α i * hermC τ G (v i) w' +
          ∑ i, ∑ k, α i * starRingEnd ℂ (β k) * hermC τ G (v i) (v k) := by
  simp only [hermC, Fin.sum_univ_two, map_sub, map_add (f := _), map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

private theorem hermC_Gm_eq_starRingEnd_swap {r : ℕ} (X : Data E r) (τ : E →+* ℂ) (v w : Fin r → ℂ) :
    hermC τ X.Gm v w = starRingEnd ℂ (hermC τ X.Gm w v) := by

  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← X.Gm_herm y x, _root_.ReciprocityTheory.ChartRestriction.G.FD.emb_cc]
  ring

private theorem hermC_zmat_mulVec_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (w w' : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.zmat u b τ) w) (Matrix.mulVec (X.zmat u b τ) w') =
      hermC τ.1 X.Gm w w' := by
  have e := hermC_sub_sum_smul_expand τ.1 X.Gm w w' (fun i => Data.emb τ.1 (u i))
    (fun i => Complex.I * (X.c τ : ℂ) * ∑ k, b τ i k * hermC τ.1 X.Gm w (Data.emb τ.1 (u k)))
    (fun i => Complex.I * (X.c τ : ℂ) * ∑ k, b τ i k * hermC τ.1 X.Gm w' (Data.emb τ.1 (u k)))
  beta_reduce at e
  rw [zmat_mulVec_eq, zmat_mulVec_eq, e]
  simp only [Fin.sum_univ_two, hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ.1, mul_zero, add_zero,
    hermC_Gm_eq_starRingEnd_swap X τ.1 (Data.emb τ.1 (u 0)) w', hermC_Gm_eq_starRingEnd_swap X τ.1 (Data.emb τ.1 (u 1)) w',
    map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
  rw [← hb τ 0 0, ← hb τ 0 1, ← hb τ 1 0, ← hb τ 1 1]
  ring

private theorem zmat_mulVec_emb_eq_self {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (i : Fin 2) :
    Matrix.mulVec (X.zmat u b τ) (Data.emb τ.1 (u i)) = Data.emb τ.1 (u i) := by
  rw [zmat_mulVec_eq]
  funext p
  simp only [hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ.1, mul_zero, Finset.sum_const_zero, zero_mul, sub_zero]

private theorem gram_zmat_mul_eq_gram {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.zmat u b τ * M) = gram τ.1 X.Gm M := by
  ext a c
  simp only [gram, Matrix.of_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.col_mul, hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ]

private theorem flowMatV_uvec_eq_zmat {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (τ : X.Ψ) :
    X.flowMatV (X.uvec u a τ) τ (s τ) =
      X.zmat u (fun τ' i k => s τ' * a τ' i * starRingEnd ℂ (a τ' k)) τ := by
  ext p j
  simp only [Data.flowMatV, Data.zmat, Data.uvec, Matrix.of_apply, Fin.sum_univ_two,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, add_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem unipotent_vector_group : UnipotentVectorGroup (E := E) := by
  unfold UnipotentVectorGroup
  intro r X u hiso
  refine ⟨fun b b' x => ?_, fun b hb => ?_⟩
  · funext τ
    show X.zmat u b τ * (X.zmat u b' τ * mat x τ) = X.zmat u (b + b') τ * mat x τ
    rw [← Matrix.mul_assoc, X.zmat_mul u hiso.1]
  · have hfix := zmat_mulVec_emb_eq_self X u hiso b
    have hdom : ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom := by
      intro x hx
      simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
      intro τ
      refine ⟨?_, fun i => ?_⟩
      · rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mat_Zb, Matrix.det_mul, X.zmat_det u hiso.1 b, one_mul]
        exact (hx τ).1
      · rw [X.dmin_Zb u hiso.1 b hb]
        exact (hx τ).2 i
    have hmaj : ∀ (x : Frame X.Ψ r) (τ : X.Ψ), x ∈ X.dom →
        X.maj (X.Zb u b x) τ (Data.emb τ.1 (u 0)) = X.maj x τ (Data.emb τ.1 (u 0)) := by
      intro x τ _
      have hv0 : ∀ w, hermC τ.1 X.Gm (Data.emb τ.1 (u 0)) (Matrix.mulVec (X.zmat u b τ) w) =
          hermC τ.1 X.Gm (Data.emb τ.1 (u 0)) w := by
        intro w
        have h := hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ (Data.emb τ.1 (u 0)) w
        rwa [hfix τ 0] at h
      simp only [Data.maj, Data.posPart, Data.gramPos, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mat_Zb, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.col_mul,
        gram_zmat_mul_eq_gram X u hiso b hb τ, hv0]
    have hD1 : ∀ x ∈ X.FramesOverBasis (u 0), X.Zb u b x ∈ X.FramesOverBasis (u 0) := by
      intro x hx
      simp only [Data.FramesOverBasis, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hdom x hx.1, fun τ => ?_⟩
      rw [hmaj x τ hx.1]
      exact hx.2 τ
    refine ⟨?_, hfix, fun τ => X.zmat_det u hiso.1 b τ, hdom, ?_, ?_, hmaj, hD1, ?_, ?_⟩
    · intro τ w w'
      exact hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ w w'
    · intro x x' h τ
      have key : ∀ y : Frame X.Ψ r,
          Set.range (fun a : Fin X.p0 => col (mat (X.Zb u b y) τ) (Fin.castLE X.p0_le a)) =
            (Matrix.mulVecLin (X.zmat u b τ)) ''
              Set.range (fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)) := by
        intro y
        rw [← Set.range_comp]
        congr 1
      rw [key x, key x', Submodule.span_image, Submodule.span_image, h τ]
    · intro la x _
      simp only [Data.nfac, X.dmin_Zb u hiso.1 b hb x]
    · intro a s x
      funext τ
      show X.zmat u b τ * (X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ) =
        X.flowMatV (X.uvec u a τ) τ (s τ) * (X.zmat u b τ * mat x τ)
      rw [flowMatV_uvec_eq_zmat X u a s τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, X.zmat_mul u hiso.1,
        X.zmat_mul u hiso.1, add_comm]
    · intro a s x
      funext τ
      exact congrArg (fun M => M * mat x τ) (flowMatV_uvec_eq_zmat X u a (fun τ => (s τ : ℂ)) τ)

end ReciprocityTheory.ChartRestriction.G.FD
