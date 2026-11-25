module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityW'

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext (zero_mul _) ?_
  change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
  apply GlobalTheory.AdelicU.af_ext
  intro w
  rw [map_mul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
    rfl
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem comm_off_of_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {m n : ℕ} {V : Spc F E m} {W : Spc F E n} {M : Model σ V W} {C : GlobalTheory.WeilM.TestClass (AF F)} {ψ : AddChar (AF F) ℂ} {om : Rep σ V W}
    (hW : GlobalTheory.WeilM.IsUSplitting C ψ M.co (GlobalTheory.WeilM.actAB (cA σ)) om)
    (g : UA σ V.J × UA σ W.J) (u : AF F)
    (hact : ∀ w, GlobalTheory.WeilM.actAB (cA σ) g (u • w) = u • w)
    (p q : Fin m × Fin n → AF F) (Φ : (Fin m × Fin n → AF F) → ℂ) (hΦ : Φ ∈ C.sp (Fin m × Fin n)) :
    om g (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om g Φ) := by
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h2 := hW.impl g (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact w] at h2
  exact h2

theorem comm_off_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {m n : ℕ} {V : Spc F E m} {W : Spc F E n} {M : Model σ V W} {C : GlobalTheory.WeilM.TestClass (AF F)} {ψ : AddChar (AF F) ℂ} {om : Rep σ V W}
    (hW : GlobalTheory.WeilM.IsUSplitting C ψ M.co (GlobalTheory.WeilM.actAB (cA σ)) om)
    (v : Pl (F := F)) (g : UA σ V.J) (hg : g ∈ UAt σ V (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin m × Fin n → AF F)
    (Φ : (Fin m × Fin n → AF F) → ℂ) (hΦ : Φ ∈ C.sp (Fin m × Fin n)) :
    om (g, 1) (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om (g, 1) Φ) :=
  comm_off_of_act hW (g, 1) u (fun w => by
    have h1 : mat g * (u • w) - u • w = (u • (mat g - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [hg u hu, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1) p q Φ hΦ

theorem comm_off_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {m n : ℕ} {V : Spc F E m} {W : Spc F E n} {M : Model σ V W} {C : GlobalTheory.WeilM.TestClass (AF F)} {ψ : AddChar (AF F) ℂ} {om : Rep σ V W}
    (hW : GlobalTheory.WeilM.IsUSplitting C ψ M.co (GlobalTheory.WeilM.actAB (cA σ)) om)
    (v : Pl (F := F)) (h : UA σ W.J) (hh : h ∈ UAt σ W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin m × Fin n → AF F)
    (Φ : (Fin m × Fin n → AF F) → ℂ) (hΦ : Φ ∈ C.sp (Fin m × Fin n)) :
    om (1, h) (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om (1, h) Φ) :=
  comm_off_of_act hW (1, h) u (fun w => by
    have h1 : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [hh u hu, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1) p q Φ hΦ

theorem locality_of_comm_off {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ) (v : Pl (F := F))
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hunit : ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) :
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) T φ (S φ) := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd
    (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h' := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h'
    exact h'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨fun φ t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)),
    fun φ hφ => ⟨?_, ?_⟩⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := fun u' hu' => funext fun i => GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ :=
      Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp
    ring

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hTr : IsTriple B G X om om') (v : Pl (F := F)) (h : UA σ G.W.J) (hh : h ∈ UAt σ G.W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin a' × Fin (a + a') → AF F)
    (Φ : (Fin a' × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a'))) :
      om' (1, h) (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (om' (1, h) Φ) :=
  comm_off_right (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil') v h hh u hu p q Φ hΦ

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v h hh φ hφ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  obtain ⟨S, hS⟩ := locality_of_comm_off B.ψ hTr.base.std v (om' (1, h))
    (fun Φ hΦ => hW.pres (1, h) Φ hΦ) (fun μ hμ Φ hΦ => hW.unit μ hμ (1, h) Φ hΦ)
    (comm_off B G X om om' hTr v h hh)
  exact ⟨S φ, hS φ hφ⟩

end GlobalTheory.WeilLocalityW'
