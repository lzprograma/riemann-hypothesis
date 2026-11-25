module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SmoothVectorsTranslateUnitary
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finset_sup_kstable {n : ℕ} (ε : Fin n → Bool) (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (s : Finset (Submodule ℂ H)) (hs : ∀ S ∈ s, FiniteDimensional ℂ S ∧ IsKStableOn ε τ S) :
    FiniteDimensional ℂ ↥(s.sup (id : Submodule ℂ H → Submodule ℂ H)) ∧
      IsKStableOn ε τ (s.sup (id : Submodule ℂ H → Submodule ℂ H)) := by
  apply _root_.Formalism.L2.SG.HCReprodM.finsetSup_kstable <;> assumption

theorem kfin_of_mem_lowKSub {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H} (hw : w ∈ lowKSub ε lam τ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ w ∈ S ∧ IsKStableOn ε τ S := by
  obtain ⟨s, hsS, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  have h := finset_sup_kstable ε τ s (fun S hS => ⟨(hsS hS).1, (hsS hS).2.1⟩)
  refine ⟨s.sup (id : Submodule ℂ H → Submodule ℂ H), h.1, ?_, h.2⟩
  rw [Finset.sup_eq_iSup]
  exact hws

theorem kfinHpk_of_lowUnitH {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w : H} (hw : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hmem⟩ := hw
  obtain ⟨S, hfd, hwS, hst⟩ := kfin_of_mem_lowKSub hmem
  exact ⟨S, hfd, hwS, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hP hst⟩

theorem zero_mem_smoothVecs (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ _
  refine ⟨Set.univ, fun _ => (0 : H), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  simp

def smoothSub (σ : Mx k r → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := smoothVecs (k := k) (r := r) σ
  add_mem' := fun h1 h2 => Formalism.MainNotions.LeviCoordinates.smooth_vectors_add h1 h2
  zero_mem' := zero_mem_smoothVecs σ
  smul_mem' := fun c _ h => Formalism.MainNotions.LeviCoordinates.smooth_vectors_smul c h

end Smooth

end Formalism.MainNotions.DoubleDerivativeSmoothness
