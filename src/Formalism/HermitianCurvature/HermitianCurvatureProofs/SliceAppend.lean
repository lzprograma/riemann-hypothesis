module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.SliceAppend

open Dx2.SL

theorem exists_append_succ {p : C.LPt} {i : ℕ} (hi : 1 ≤ i) (hp : D.IsLocPt p i) :
    ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by
  have hne : p ≠ [] := by
    rintro rfl
    have := hp.2
    simp [D.ptSize] at this
    omega
  refine ⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩
  have h1 : 1 ≤ (p.getLast hne).1 := (hp.1 _ (List.getLast_mem hne)).1
  rw [Nat.sub_add_cancel h1]
  exact (List.dropLast_append_getLast hne).symm

theorem perm_append {h : C.LPt} {n : ℕ} {t : ℂ}
    (hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])))
    (q : Fin (D.ptSize (h ++ [(n + 1, t)]))) :
    (sigP (n := n) (D.ptPerm h) (Fin.cast (ptSize_append h (n + 1) t) q)).val =
      (D.ptPerm (h ++ [(n + 1, t)]) q).val := by
  have hP := ptSize_append h (n + 1) t
  have hlocH := isLocPt_head hloc
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  rw [hspec q, partner_append (n + 1) t h q.val (by have := q.isLt; omega)]
  by_cases h1 : q.val < D.ptSize h
  · rw [ite_eq_left h1]
    have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
    rw [e, blockPerm_castAdd]
    exact hspec' ⟨q.val, h1⟩
  · rw [ite_eq_right h1]
    have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, blockPerm_natAdd]
    simp only [Fin.val_natAdd, Fin.val_rev]
    omega

theorem diag_append (h : C.LPt) (n : ℕ) (t : ℂ)
    (q : Fin (D.ptSize (h ++ [(n + 1, t)]))) :
    dP (n := n) (D.ptDiag h) t (Fin.cast (ptSize_append h (n + 1) t) q) =
      D.ptDiag (h ++ [(n + 1, t)]) q := by
  have hP := ptSize_append h (n + 1) t
  simp only [D.ptDiag]
  rw [scal_append (n + 1) t h q.val (by have := q.isLt; omega)]
  by_cases h1 : q.val < D.ptSize h
  · rw [ite_eq_left h1]
    have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
    rw [e, dP, Fin.addCases_left]; rfl
  · rw [ite_eq_right h1]
    have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, dP, Fin.addCases_right]

theorem diag_append_ne_zero {h : C.LPt} {n : ℕ} {t : ℂ}
    (hd0 : ∀ q, D.ptDiag h q ≠ 0) (ht : t ≠ 0) (q : Fin (D.ptSize h + (n + 1))) :
    dP (n := n) (D.ptDiag h) t q ≠ 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) q
  · simpa only [dP, Fin.addCases_left] using hd0 i
  · simpa only [dP, Fin.addCases_right] using ht

theorem slice_append {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E)
    (h : C.LPt) (n : ℕ) (t : ℂ)
    (hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])))
    (hle : D.ptSize (h ++ [(n + 1, t)]) ≤ r)
    (γ : B.Mat k (r - D.ptSize (h ++ [(n + 1, t)]))) :
    let ρ := r - D.ptSize (h ++ [(n + 1, t)])
    D.sliceAt k r z z' F (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := D.ptSize h + (n + 1)) (s := 0) k ρ (sigP (D.ptPerm h))
        (dP (D.ptDiag h) t)
        (D.castV (by have := ptSize_append h (n + 1) t; omega) z)
        (D.castV (by have := ptSize_append h (n + 1) t; omega) z')
        (D.castF (by have := ptSize_append h (n + 1) t; omega) F) (fun a => a.elim0) γ := by
  have hP := ptSize_append h (n + 1) t
  let ρ := r - D.ptSize (h ++ [(n + 1, t)])
  obtain ⟨-, hT⟩ := phi_transport (k := k) (ρ := ρ) hP _ _ (perm_append hloc) _ _ (diag_append h n t)
    (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (b := r) (by omega) F) γ
  unfold D.sliceAt
  rw [dite_eq_left hle, hT]
  simp only [castV_castV, castF_castF]
  rfl

end Formalism.FourierDecayAlt.P.SliceAppend
