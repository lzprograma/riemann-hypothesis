module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Alg

variable {R : Type} [CommRing R] {r : ℕ}

def headCols (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Submodule R (Fin (r + 1) → R) :=
  Submodule.span R (Set.range fun a : Fin r => fun i => Z i a.castSucc)

abbrev MbMod (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Type :=
  (Fin (r + 1) → R) ⧸ headCols Z

def bCls (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : MbMod Z :=
  Submodule.Quotient.mk (fun i => Z i (Fin.last r))

def eCl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : MbMod Z :=
  Submodule.Quotient.mk (Pi.single (Fin.last r) 1)

def IsoMbe (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Type :=
  {γ : MbMod Z₁ ≃ₗ[R] MbMod Z₂ // γ (bCls Z₁) = bCls Z₂ ∧ γ (eCl Z₁) = eCl Z₂}

end Alg

section Props

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def headDet (M : Model F E) {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) : E :=
  ((Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc).det

end Props

section Lemmas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem zzplusOf_none (hs : M.split = none) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : F) : HermSp.ZZplusOf M Zh T T' = Zh := by
  unfold HermSp.ZZplusOf
  rw [hs]

theorem dl_eq_det (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
  unfold HermSp.Dl
  rw [dite_eq_left (Nat.le_succ r)]
  rfl

theorem dl_succ_unit {H : HermSp M V} {r : ℕ} {t₁ : Term V M r} {f₂ f₂' : Fin (r + 1) → V}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'} (hyp : LocalCountHypotheses H t₁ f₂ f₂' φ φ') :
    IsUnit (H.Dl t₁.f t₁.f' (r + 1)) :=
  hyp.1.1.2.2.2.1

end Lemmas

end Formalism.L2.SG.LocalCountModules.LocCntCommon
