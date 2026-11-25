module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct

namespace GlobalTheory.StdCharLocal

theorem psiV_ne_one_of_trace {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  first | exact _root_.GlobalTheory.StdCharTotReal.psiV_ne_one_of_trace | exact @_root_.GlobalTheory.StdCharTotReal.psiV_ne_one_of_trace | apply _root_.GlobalTheory.StdCharTotReal.psiV_ne_one_of_trace <;> assumption

theorem psiV_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  intro D ψ hψ v
  have h := GlobalTheory.StdAdelicChar.isStdChar_inv hψ
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨y, hy⟩ := psiV_ne_one_of_trace h.1 (fun a => by
    rw [h.2.2 θ hθ, GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _,
      GlobalTheory.StdRat.sum_tauE_eq_trace]
    simp) v
  refine ⟨y, fun h1 => hy ?_⟩
  rw [psiV] at h1 ⊢
  rw [AddChar.inv_apply', h1, inv_one]

end GlobalTheory.StdCharLocal
