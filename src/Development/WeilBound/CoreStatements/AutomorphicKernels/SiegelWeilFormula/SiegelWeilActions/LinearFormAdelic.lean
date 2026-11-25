module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def linearFormAdelic (δ : E) : AE F E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    LinearMap.baseChange (AF F) (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1)

theorem inclR_eq' (x : E) : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ[F] x := rfl

theorem ell_spec {δ : E} (hδ0 : δ ≠ 0) : (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) δ = 1 := by
  have hex : ∃ ℓ : E →ₗ[F] F, δ ≠ 0 → ℓ δ = 1 :=
    (Module.Projective.exists_dual_eq_one F hδ0).imp fun _ h _ => h
  exact Classical.epsilon_spec hex hδ0

theorem ellA_smul_inclR {δ : E} (hδ0 : δ ≠ 0) (a : AF F) : linearFormAdelic (F := F) δ (a • inclR (F := F) (AF F) δ) = a := by
  rw [inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [linearFormAdelic, LinearMap.baseChange_tmul, ell_spec hδ0]

theorem ellA_inclR (δ : E) (e : E) : ∃ f : F, linearFormAdelic (F := F) δ (inclR (F := F) (AF F) e) = algebraMap F (AF F) f := by
  refine ⟨(Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) e, ?_⟩
  rw [inclR_eq']
  simp [linearFormAdelic, LinearMap.baseChange_tmul, Algebra.algebraMap_eq_smul_one]

theorem continuous_ellA (δ : E) : Continuous (linearFormAdelic (F := F) (E := E) δ) :=
  IsModuleTopology.continuous_of_linearMap (R := AF F) (linearFormAdelic (F := F) (E := E) δ)

end PositivityTheory.SiegelWeilFormula.Act.C5.Meas

end
