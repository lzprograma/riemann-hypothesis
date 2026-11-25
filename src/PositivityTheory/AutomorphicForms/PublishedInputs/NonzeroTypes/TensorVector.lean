module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
import Mathlib.Algebra.Module.StablyFree.Basic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TprodNeZeroOfNe

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

namespace TensorVector

end TensorVector

theorem step_tensorVec : TensorProductVectors := by
  intro k _ _ _ _ s d X _ _ σ μ h
  choose x hx0 hx using h
  refine ⟨PiTensorProduct.tprod ℂ x, GlobalTheory.Contr.tprod_ne_zero_of_ne x hx0, fun m hm => ?_⟩
  rw [piTensor_tprod]
  have : (fun a => σ a (m a) (x a)) =
      fun a => ((μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ) • x a :=
    funext fun a => hx a (m a) (hm a)
  rw [this, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]

end UpperTheory.TNZ
