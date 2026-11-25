module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

section Lead

variable {K : Type*} [CommRing K]

def leadM {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (l : ℕ) : K :=
  if hl : l ≤ m then (X.submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0

theorem sum_castLE {A : Type*} [AddCommMonoid A] {l m : ℕ} (hl : l ≤ m) (g : Fin m → A)
    (hg : ∀ a : Fin m, l ≤ a.val → g a = 0) : ∑ a, g a = ∑ a : Fin l, g (Fin.castLE hl a) := by
  have e : ∑ a : Fin l, g (Fin.castLE hl a) = ∑ a ∈ Finset.univ.map (Fin.castLEEmb hl), g a := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hg
  by_contra h
  exact ha (Finset.mem_map.2 ⟨⟨a.val, Nat.lt_of_not_le h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem leadM_mul {m : ℕ} {L X U : Matrix (Fin m) (Fin m) K} (hL : IsLo L) (hU : IsUp U) (l : ℕ) :
    leadM (L * X * U) l = leadM X l := by
  unfold leadM
  split_ifs with hl
  · have e : (L * X * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        L.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      refine (sum_castLE hl _ ?_).trans (Finset.sum_congr rfl fun b _ => ?_)
      · intro b hb
        have hj := j.isLt
        rw [hU.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
      · congr 1
        refine sum_castLE hl _ fun a ha => ?_
        have hi := i.isLt
        rw [hL.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
    rw [e, Matrix.det_mul, Matrix.det_mul]
    have h1 : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_lo' ⟨fun a => hL.1 _, fun a b hab => hL.2 _ _ hab⟩
    have h2 : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_up' ⟨fun a => hU.1 _, fun a b hab => hU.2 _ _ hab⟩
    rw [h1, h2, one_mul, mul_one]
  · rfl

end Lead

section Mats

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)

def mkMat {m : ℕ} (P : Matrix (Fin m) (Fin m) E) (hP : ∀ a b, P a b ∈ M.R) (hu : IsUnit P.det) : M.Mat m :=
  ⟨Matrix.of fun a b => ⟨P a b, hP a b⟩, by
    have : (Matrix.of fun a b => (⟨P a b, hP a b⟩ : M.R)).map M.R.subtype = P := rfl
    rw [this]; exact hu⟩

theorem clsOf_mk {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hP : ∀ a b, P a b ∈ M.R)
    (hu : IsUnit P.det) : clsOf M P = some (Quotient.mk (M.isoSetoid m) (mkMat M P hP hu)) := by
  unfold clsOf
  rw [dite_eq_left ⟨hP, hu⟩]
  rfl

theorem clsOf_map {m : ℕ} (Z : M.Mat (m + 1)) :
    clsOf M (Z.Z.map M.R.subtype) = some (Quotient.mk (M.isoSetoid m) Z) := by
  exact clsOf_mk M (Z.Z.map M.R.subtype) (fun a b => (Z.Z a b).2) Z.unit

theorem nIso_mk_out {m : ℕ} (Z₁ Z₂ : M.Mat (m + 1)) :
    M.nIso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) =
      M.nIso Z₁ Z₂ := by
  have h1 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) Z₁) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₁
  have h2 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) Z₂) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₂
  exact nIso_congr M h1.some h2.some

end Mats

section Cut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def LeadZZ : Prop :=
  ∀ (p : PlF D) (Zh : MatP D p) (T T' : (D.s.atP p).Fp),
    (leadM Zh D.R.rS = 0 ↔ leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS = 0) ∧
    (IsUnit (leadM Zh D.R.rS) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS)) ∧
    (leadM Zh D.R.rS = 0 → IsUnit (leadM Zh (D.R.rS + 1)) →
      IsUnit (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T').det)

def ModKind : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)),
    (Dmin w D.R.rS = 0 → leadM (modMat Zd.δ T T' p w) D.R.rS = 0) ∧
    (Dmin w D.R.rS ≠ 0 → IsUnit (leadM (modMat Zd.δ T T' p w) D.R.rS) ∧
      (∀ a : Fin D.R.rS, modMat Zd.δ T T' p w a.castSucc (Fin.last D.R.rS) = 0 ∧
        modMat Zd.δ T T' p w (Fin.last D.R.rS) a.castSucc = 0) ∧
      modMat Zd.δ T T' p w (Fin.last D.R.rS) (Fin.last D.R.rS) =
        blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) ∧
      IsUnit (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep)))

theorem add_cornE_zero (p : PlF D) (X : MatP D p) : X + cornE p 0 = X := by
  ext a b; simp [cornE]

theorem loUp_of_hyp {p : PlF D} {uL uU : MatP D p} (h1 : ∀ a, uL a a = 1 ∧ uU a a = 1)
    (h2 : ∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) : IsLo uL ∧ IsUp uU :=
  ⟨⟨fun a => (h1 a).1, fun a b hab => (h2 a b hab).1⟩, ⟨fun a => (h1 a).2, fun a b hab => (h2 a b hab).2⟩⟩



end Cut

end Formalism.L2.SG.Pf.PCount
