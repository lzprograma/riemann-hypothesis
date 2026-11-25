module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfCo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTop
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation

def QuadCoord : Prop :=
  ∀ (V H : Type) [AddCommGroup V] [TopologicalSpace V] [AddCommGroup H] [TopologicalSpace H]
    (n m : ℕ) (eV : V ≃ₜ (Fin n → ℝ)) (eH : H ≃ₜ (Fin m → ℝ)) (Q : V → H) (β : V → V → H),
    (∀ x y, eV (x + y) = eV x + eV y) → (∀ x y, eH (x + y) = eH x + eH y) →
    Continuous (fun p : V × V => β p.1 p.2) → (∀ x y z, β (x + y) z = β x z + β y z) →
    (∀ x y, β x y = β y x) → (∀ x, β x x = Q x + Q x) →
    ContDiff ℝ 1 (fun y => eH (Q (eV.symm y))) ∧
      ∀ x y, fderiv ℝ (fun y => eH (Q (eV.symm y))) (eV x) (eV y) = eH (β x y)

theorem quadCoord_holds : QuadCoord := by
  intro V H _ _ _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  have hVs : ∀ y z, eV.symm (y + z) = eV.symm y + eV.symm z := by
    intro y z; apply eV.injective; rw [hV]; simp
  let b : (Fin n → ℝ) → (Fin n → ℝ) → (Fin m → ℝ) := fun y z => eH (β (eV.symm y) (eV.symm z))
  have hb1 : ∀ y y' z, b y z + b y' z = b (y + y') z := by
    intro y y' z; simp only [b, hVs, hβa, hH]
  have hb2 : ∀ y z z', b y (z + z') = b y z + b y z' := by
    intro y z z'; simp only [b, hVs]
    rw [hβs, hβa, hH, hβs (eV.symm z), hβs (eV.symm z')]
  have hbc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => b p.1 p.2) :=
    eH.continuous.comp (hβc.comp ((eV.symm.continuous.comp continuous_fst).prodMk
      (eV.symm.continuous.comp continuous_snd)))
  let L1 : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := fun y =>
    AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (b y) (hb2 y))
      (hbc.comp (continuous_const.prodMk continuous_id))
  have hL1 : ∀ y z, L1 y z = b y z := fun _ _ => rfl
  have hsm1 : ∀ (c : ℝ) y z, b (c • y) z = c • b y z := by
    intro c y z
    have : b (c • y) z = c • b y z := (AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (fun y => b y z)
      (fun y y' => (hb1 y y' z).symm)) (hbc.comp (continuous_id.prodMk continuous_const))).map_smul c y
    exact this
  let Bl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toFun := L1
      map_add' := fun y y' => by ext1 z; simp only [add_apply, hL1, hb1]
      map_smul' := fun c y => by
        ext1 z; simp only [smul_apply, hL1, hsm1, RingHom.id_apply] }
  let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := LinearMap.toContinuousLinearMap Bl
  have hB : ∀ y z, B y z = b y z := fun _ _ => rfl
  have hf : ∀ y, eH (Q (eV.symm y)) = (1/2 : ℝ) • B y y := by
    intro y
    rw [hB]
    simp only [b, hQ, hH]
    rw [← two_smul ℝ (eH (Q (eV.symm y))), smul_smul]
    norm_num
  have hfe : (fun y => eH (Q (eV.symm y))) = fun y => (1/2 : ℝ) • B y y := funext hf
  have hd : ∀ y, HasFDerivAt (fun y => (1/2 : ℝ) • B y y)
      ((1/2 : ℝ) • (B.precompR (Fin n → ℝ) y (ContinuousLinearMap.id ℝ _) +
        B.precompL (Fin n → ℝ) (ContinuousLinearMap.id ℝ _) y)) y :=
    fun y => by
      have h := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).const_smul
        (1/2 : ℝ)
      exact h
  refine ⟨?_, fun x y => ?_⟩
  · rw [hfe]
    exact (B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).const_smul
      (1/2 : ℝ)
  · rw [hfe, (hd _).fderiv]
    show (1/2 : ℝ) • (B (eV x) (eV y) + B (eV y) (eV x)) = eH (β x y)
    rw [hB, hB]
    simp only [b, Homeomorph.symm_apply_apply]
    rw [hβs y x, ← two_smul ℝ (eH (β x y)), smul_smul]
    norm_num

section B

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => hR R σ J (X i) (Y j) + hR R σ J (Y i) (X j)

export PI.VolStabSW (hR_add_left hR_add_right hR_herm gramB_mem)

end B

section BTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

export PI.VolStabSW (continuous_gramB_apply continuous_gramB)

end BTop

def TensR : Prop := InCtx fun F E _ _ _ _ _ σ M _ a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y

def FreeSurj : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
    ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S

theorem coordInf_of (h1 : QuadCoord) (h2 : TensR) (h3 : FreeSurj) : CoordInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  obtain ⟨n, m, eV, eH, hV, hH⟩ := h2 F E σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a := gramH (Ainf F) σ hσ J hJ.1
  let β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) →
      HermR (Ainf F) σ a := fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩
  have hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2) := by
    exact (continuous_gramB (Ainf F) σ J).subtype_mk _
  have hβa : ∀ x y z, β (x + y) z = β x z + β y z := by
    intro x y z; apply Subtype.ext; funext i j
    show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    abel
  have hβs : ∀ x y, β x y = β y x := by
    intro x y; apply Subtype.ext; funext i j
    simp only [β, gramB]; exact add_comm _ _
  have hQ : ∀ x, β x x = Q x + Q x := by
    intro x; apply Subtype.ext; funext i j; rfl
  obtain ⟨hC, hD⟩ := h1 _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  refine ⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩
  · simp [Q, gramH]
  · intro t
    obtain ⟨Y, hY⟩ := h3 F E σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet X hX (eH.symm t)
    refine ⟨eV Y, ?_⟩
    rw [hD X Y]
    have : β X Y = eH.symm t := Subtype.ext hY
    rw [this, Homeomorph.apply_symm_apply]

theorem densInf_of_tens (h2 : TensR) (h3 : FreeSurj) : DensInf :=
  densInf_of_coord (coordInf_of quadCoord_holds h2 h3)

end PI.VolStabS
