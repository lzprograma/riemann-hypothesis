module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads

@[expose] public section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

def PStdC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2)

theorem pStdC_of (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) : PStdC :=
  Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT

theorem decay_scale (lam x : ℝ) (hlam : 0 < lam) (hx : 0 ≤ x) :
    ((1 + lam * x) ^ 3)⁻¹ ≤ (max 1 lam⁻¹) ^ 3 * ((1 + x) ^ 3)⁻¹ := by
  have hM : 1 ≤ max 1 lam⁻¹ := le_max_left _ _
  have hle : 1 + x ≤ max 1 lam⁻¹ * (1 + lam * x) := by
    rcases le_or_gt 1 lam with h1 | h1
    · have e1 : x ≤ lam * x := le_mul_of_one_le_left hx h1
      have e2 : 1 + lam * x ≤ max 1 lam⁻¹ * (1 + lam * x) := le_mul_of_one_le_left (by positivity) hM
      linarith
    · have hi : lam⁻¹ ≤ max 1 lam⁻¹ := le_max_right _ _
      have e : lam⁻¹ * (1 + lam * x) = lam⁻¹ + x := by field_simp
      have h2 : 1 ≤ lam⁻¹ := by rw [le_inv_comm₀ one_pos hlam]; simpa using h1.le
      nlinarith [mul_le_mul_of_nonneg_right hi (by positivity : (0 : ℝ) ≤ 1 + lam * x)]
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + lam * x := by positivity
  have hc : (1 + x) ^ 3 ≤ (max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h1.le hle 3
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ((1 + lam * x) ^ 3)⁻¹ * (1 + x) ^ 3 ≤ ((1 + lam * x) ^ 3)⁻¹ * ((max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (max 1 lam⁻¹) ^ 3 := by field_simp

section frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Kg (S : C.HidaSetting E Wp Wq) (j : ℕ) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j

theorem gramLoc_setC_app {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) (c : ℂ) (hc : c ≠ 0) :
    (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) =
      ((Kg S j h h' : ℝ) : ℂ) * ((KB.levW (D.parOf S v) (j + 1) ((lamS S j : ℂ) * c) : ℝ) : ℂ) *
        (p v).RR (F v ε) (j + 1) w (stdS S h ++ [(1, (lamS S j : ℂ) * c)])
          (stdS S h' ++ [(1, (lamS S j : ℂ) * c)]) := by
  have hmul := nnS_app_rr_mul hB F v ε j hj w h h' hsz hsz' c hc
  have hb1 : bS S (h ++ [(1, c)]) = bS S h := bSt_append_one _ _ _
  have hb2 : bS S (h' ++ [(1, c)]) = bS S h' := bSt_append_one _ _ _
  rw [gramLoc_setC hB, stdS_app S j h c hsz, stdS_app S j h' c hsz', hb1, hb2]
  unfold Kg
  push_cast at hmul ⊢
  linear_combination (1 / ((bS S h : ℂ) * (bS S h' : ℂ) * (ΓS S (j + 1) : ℂ))) * hmul

theorem int_gramLoc_setC (hPS : PStdC) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (hF : KB.CptCoef (p v).T.base (F v ε)) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j) :
    ∫ c : ℂ, (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c =
      ((Kg S j h h' * |(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)) := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
  have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
  obtain ⟨φ, -, -, hφ, hφint⟩ := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w
    (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) hF (by rw [hl0]; exact hw)
  have hlam_pos := lamS_pos S hgpos j
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c' := ⟨_, rfl⟩
  have hae : (fun c : ℂ => (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) *
      KB.psiL S l c) =ᵐ[volume] fun c => ((Kg S j h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    filter_upwards [ae_ne_zero_complex] with c hc
    have hlc : (lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
    simp only [hgdef, Complex.real_smul]
    rw [gramLoc_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc, psiL_eq_fsv S hgpos j l c]
    ring
  rw [integral_congr_ae hae, integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex,
    Complex.real_smul, hgdef]
  simp only
  rw [hφint (sW S j l)]
  push_cast
  ring

end frame

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay
