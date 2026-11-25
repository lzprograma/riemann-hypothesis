module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.SharpEquivApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Mathlib.RingTheory.PiTensorProduct
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Coord

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

abbrev Ix (r : ℕ) : Type := Fin (r + 1) ⊕ Fin (r + 1)

def gramC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Matrix (Ix r) (Ix r) E :=
  Matrix.fromBlocks (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (Matrix.of fun a b => cj (Z a b)) Z.transpose
    (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T' else 0)

def relC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Submodule O (Ix r → O) where
  carrier := {y | ∃ c : Ix r → O, ∀ j, (y j : E) = ∑ i, (c i : E) * gramC cj Z T T' i j}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun j => ?_⟩
    simp only [Pi.add_apply, Subring.coe_add, hc j, hd j, add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, fun j => by simp⟩
  smul_mem' := by
    rintro a y ⟨c, hc⟩
    refine ⟨a • c, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hc j, Finset.mul_sum, mul_assoc]

abbrev DDc (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Type :=
  (Ix r → O) ⧸ relC O cj Z T T'

def formC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W : Ix r → O) : E :=
  ∑ i, ∑ j, (Y i : E) * (gramC cj Z T T')⁻¹ i j * cj (W j)

def lamC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) : E :=
  (Z⁻¹.mulVec y) (Fin.last r)

def lamStarC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) : E :=
  ∑ b, cj (Z⁻¹ b (Fin.last r)) * y b

def GamC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Set (DDc O cj Z T T' × (E × E)) :=
  {p | ∃ Y : Ix r → O, (∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) ∧
    p = (Submodule.Quotient.mk Y, ((Y (Sum.inl (Fin.last r)) : E),
      lamStarC cj Z (fun b => (Y (Sum.inr b) : E))))}

def GamC' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Set (DDc O cj Z T T' × (E × E)) :=
  {p | ∃ Y : Ix r → O, (∀ b : Fin r, Y (Sum.inr b.castSucc) = 0) ∧
    p = (Submodule.Quotient.mk Y, (lamC Z (fun a => (Y (Sum.inl a) : E)),
      (Y (Sum.inr (Fin.last r)) : E)))}

def ThetaC (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) :
    Set (DDc O cj Z₁ T T' ≃ₗ[O] DDc O cj Z₂ T T') :=
  {θ | (∀ Y W Y₂ W₂ : Ix r → O, θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ →
      θ (Submodule.Quotient.mk W) = Submodule.Quotient.mk W₂ →
      formC O cj Z₂ T T' Y₂ W₂ - formC O cj Z₁ T T' Y W ∈ O) ∧
    (fun p => (θ p.1, p.2)) '' GamC O cj Z₁ T T' = GamC O cj Z₂ T T' ∧
    (fun p => (θ p.1, p.2)) '' GamC' O cj Z₁ T T' = GamC' O cj Z₂ T T'}

end Coord

section Deriv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem dl_full (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dite_eq_left le_rfl]
  congr 1

theorem gramC_eq (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T') =
      (H.gram (Sum.elim f f')).transpose := by
  rw [gram_eq_fromBlocks H f f' T T' hF hF', Matrix.fromBlocks_transpose]
  ext (a | a) (b | b) <;> simp [gramC, cornerM, Function.swap, and_comm]

end Deriv

end Formalism.L2.SG.LocalCountModules.LocCntCommon
