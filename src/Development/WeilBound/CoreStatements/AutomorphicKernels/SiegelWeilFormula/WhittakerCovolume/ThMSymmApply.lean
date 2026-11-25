module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThInclRInjective

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

instance th_borelUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

instance th_borelHA {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J) := ⟨rfl⟩

theorem th_sigR_incl (x : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ (inclR (F := F) (E := E) (AF F) x) = inclR (F := F) (E := E) (AF F) (σ x) := by
  simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem th_cT_map {M : ℕ} (γ : Matrix (Fin M) (Fin M) E) :
    (HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) γ).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (γ.map (inclR (F := F) (E := E) (AF F))) := by
  ext i j
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.cT, Matrix.map_apply, Matrix.transpose_apply]
  exact (th_sigR_incl _).symm

end PositivityTheory.SiegelWeilFormula.KWhit

end
