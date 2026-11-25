module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def thW (B : Base F E) (w : InfinitePlace F) : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ :=
  (starRingEnd ℂ).comp ((infEmb (B.emb w)).comp
    (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom)

def cW (B : Base F E) (η : E) (w : InfinitePlace F) : ℂ := ((‖(B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

theorem cW_ne (B : Base F E) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) : cW B η w ≠ 0 := by
  have h1 : (B.emb w).1 η ≠ 0 := (map_ne_zero _).2 hη
  have h2 : 0 < ‖(B.emb w).1 η‖ := norm_pos_iff.2 h1
  unfold cW
  exact_mod_cast (Real.rpow_pos_of_pos h2 _).ne'

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
