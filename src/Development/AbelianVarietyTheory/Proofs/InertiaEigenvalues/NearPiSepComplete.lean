module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOne

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

theorem sep_complete_of_coord {R A B I : Type} [AddCommGroup R] [CommRing A] [CommRing B]
    (φ : I → R →+ B) (j : A →+* B) (hj : Function.Injective j) (t : A)
    (hs : ∀ c : I → A, ∃ x : R, ∀ i, φ i x = j (c i))
    (h1 : ∀ x : A, (∀ m : ℕ, t ^ m ∣ x) → x = 0)
    (h2 : ∀ a : ℕ → A, ∃ x : A, ∀ m : ℕ, t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i) :
    (∀ x : R, (∀ (m : ℕ) i, ∃ c, φ i x = j (t ^ m * c)) → ∀ i, φ i x = 0) ∧
    ∀ (k : ℕ) (f : ℕ → R), (∀ n i, ∃ c, φ i (f n) = j (t ^ (n + k) * c)) →
      ∃ x, ∀ (m : ℕ) i, ∃ c, φ i (x - ∑ n ∈ Finset.range m, f n) = j (t ^ (m + k) * c) := by
  refine ⟨fun x hx i => ?_, fun k f hf => ?_⟩
  · obtain ⟨y, hy⟩ := hx 0 i
    rw [pow_zero, one_mul] at hy
    have hdiv : ∀ m : ℕ, t ^ m ∣ y := by
      intro m
      obtain ⟨c, hc⟩ := hx m i
      exact ⟨c, hj (hy.symm.trans hc)⟩
    rw [hy, h1 y hdiv, map_zero]
  · choose c hc using hf
    choose y hy using fun i => h2 (fun n => c n i)
    obtain ⟨x, hx⟩ := hs (fun i => t ^ k * y i)
    refine ⟨x, fun m i => ?_⟩
    obtain ⟨d, hd⟩ := hy i m
    refine ⟨d, ?_⟩

    rw [map_sub, map_sum, hx i, Finset.sum_congr rfl (fun n _ => hc n i), ← map_sum j, ← map_sub j]
    congr 1
    have e : t ^ k * y i - ∑ n ∈ Finset.range m, t ^ (n + k) * c n i =
        t ^ k * (y i - ∑ n ∈ Finset.range m, t ^ n * c n i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e, hd]
    ring

def crdZero {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    RW LL →+ Cb l :=
  (WittVector.constantCoeff : WCb l →+* Cb l).toAddMonoidHom.comp
    (crd (W := WCb l) (basisO LL) i).toAddMonoidHom

theorem crdZero_apply {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i) (x : RW LL) :
    crdZero LL i x = (crd (basisO LL) i x).coeff 0 := rfl

private theorem crd_tmul_lemma {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (o : ↥(OL LL)) (w : WCb l) :
    crd (W := WCb l) (basisO LL) i (o ⊗ₜ[ℤ_[l]] w) = (basisO LL).coord i o • w := by
  unfold crd
  rfl


private theorem crd_sum_lemma_4 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (w : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → WCb l) :
    crd (W := WCb l) (basisO LL) i (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] w k) = w i := by

  simp [map_sum, Finsupp.single_apply]

private theorem surj_lemma_14 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (c : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l) :
    ∃ x : RW LL, ∀ i, crdZero LL i x = algebraMap (OCb l) (Cb l) (c i) := by
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (algebraMap (OCb l) (Cb l) (c k)),
    fun i => ?_⟩
  rw [crdZero_apply, crd_sum_lemma_4, WittVector.teichmuller_coeff_zero]

theorem nearPi_sep_complete (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧
    ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) →
      ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  have key := sep_complete_of_coord (fun i => crdZero LL i) (algebraMap (OCb l) (Cb l))
    (IsFractionRing.injective (OCb l) (Cb l)) (AI.εroot s - 1) (surj_lemma_14 LL)
    (_root_.GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 (_root_.GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).2
  refine ⟨fun x hx => ?_, fun k f hf => ?_⟩
  · refine (dvd_iff_crd LL x).mpr fun i => ?_
    rw [← crdZero_apply]
    exact key.1 x (fun m i => (nearPi_iff_crd AI LL s m x).1 (hx m) i) i
  · obtain ⟨x, hx⟩ := key.2 k f (fun n i => (nearPi_iff_crd AI LL s (n + k) (f n)).1 (hf n) i)
    exact ⟨x, fun m => (nearPi_iff_crd AI LL s (m + k) _).2 (hx m)⟩

end GlobalTheory.Decompl
