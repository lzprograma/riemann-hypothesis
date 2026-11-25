module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsLocUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sc1 {R : Type} [CommRing R] : Rˣ →* GL (Fin 1) R :=
  Units.map (Matrix.scalar (Fin 1) : R →+* Matrix (Fin 1) (Fin 1) R).toMonoidHom

omit [NumberField F] [NumberField E] in
theorem det_sc1 {R : Type} [CommRing R] (x : Rˣ) : Matrix.GeneralLinearGroup.det (sc1 x) = x := by
  ext
  simp [sc1, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

omit [NumberField F] [NumberField E] in
theorem map_det_bc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (γ : GL (Fin 1) R) :
    Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det γ) = Matrix.GeneralLinearGroup.det (Formalism.UG.bc f γ) := by
  ext
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply]
  rw [RingHom.map_det]
  rfl

end PositivityTheory.SiegelWeilFormula.Ldexb

end
