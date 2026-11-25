module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per

theorem _root_.GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective : ∀ (l : ℕ) [Fact l.Prime] (c : Core l), c.TensorInj := by
  first | exact @GlobalTheory.MemLoc.TensorInj.tensorInj
