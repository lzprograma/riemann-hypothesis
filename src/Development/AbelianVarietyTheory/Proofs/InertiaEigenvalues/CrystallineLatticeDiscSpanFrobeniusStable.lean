module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisenstein

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem mulVec_frob_of_unit {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (j : R →+* D) (Φ : D →+* D)
    (Ψ : R →+* R) (h : ∀ r, j (Ψ r) = Φ (j r)) (c : Rˣ) (W : Matrix (Fin d) (Fin d) D)
    (B : Matrix (Fin d) (Fin d) R) (hW : j c • W.map Φ = W * B.map j) (x : Fin d → R) :
    W *ᵥ (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      fun a => Φ ((W *ᵥ fun b => j (x b)) a) := by
  have e1 : (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      j ((c⁻¹ : Rˣ) : R) • (B.map j *ᵥ fun b => Φ (j (x b))) := by
    funext a

    simp [Matrix.mulVec, dotProduct, map_sum, h]
  have e2 : (fun a => Φ ((W *ᵥ fun b => j (x b)) a)) = W.map Φ *ᵥ fun b => Φ (j (x b)) := by
    funext a

    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e1, e2, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hW, Matrix.smul_mulVec, smul_smul, ← map_mul,
    Units.inv_mul, map_one, one_smul]

theorem span_frobenius_stable_of_frob_eq_mul (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K)
    (d : ℕ) (W : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (B : Matrix (Fin d) (Fin d) bk.S) (c N : ℕ)
    (hW : ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀,
      IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ →
        ((l : bk.DA bk.ρ₀) ^ c * bk.iS (frobS l bk.a bk.E) ^ N) • W.map Φ = W * B.map bk.iS)
    (y : Fin d → Ainf l)
    (hy : ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀,
      IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) :
    ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀,
      IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j →
        W *ᵥ (fun a => j (x a)) = fun a => bk.iA (WittVector.frobenius (y a)) := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := _root_.GlobalTheory.BSP.flat_disc l K bk
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l bk.S bk.S (frobS l bk.a) X X bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hu : IsUnit (((l : ℕ) : bk.DS bk.ρ₀) ^ c *
      toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ N) :=
    ((isUnit_l_disc l (X : bk.S) bk.ρ₀).pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun a => ((u⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) *
    (B.map (toDisc l (X : bk.S) bk.ρ₀) *ᵥ fun b => Ψ (x b)) a, fun j hj => ?_⟩
  have hcomm : j.comp Ψ = Φ.comp j := by
    refine IsDiscMap.unique (DiscBasic.isDiscMap_comp l _ _ hΨ hj) ?_
    have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
      RingHom.ext bk.ev_frob
    rw [e]
    exact DiscBasic.isDiscMap_comp l _ _ hj hΦ
  have hWΦ := hW Φ hΦ
  rw [mulVec_frob_of_unit j Φ Ψ (RingHom.congr_fun hcomm) u W _ ?_ x, hx j hj]
  · funext a
    exact hΦ.ext _
  · rw [hu, map_mul, map_pow, map_pow, map_natCast, hj.ext, Matrix.map_map]
    refine hWΦ.trans ?_
    congr 2
    funext a
    exact (hj.ext a).symm

end GlobalTheory.BSP
