module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) :=
  by apply _root_.GlobalTheory.ThK.Dbl.Euler.lcsc_UA <;> assumption

theorem continuous_ht (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (ht : UA σ J → ℝ≥0) := by
  exact (GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val

theorem grpTop_of : GrpTop := by
  unfold GrpTop
  intro F E _ _ _ _ _ σ _ n J _
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hM : Countable (Matrix (Fin n) (Fin n) E) := by
    unfold Matrix
    infer_instance
  have hG : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) (fun a b hab => Units.ext hab)
  let f := Matrix.GeneralLinearGroup.map (n := Fin n)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F))
  have hR : Countable (Set.range f) := (Set.countable_range f).to_subtype
  refine ⟨(lcsc_UA σ J).1, (lcsc_UA σ J).2.1, (lcsc_UA σ J).2.2, ?_,
    GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J,
    Units.continuous_val.comp continuous_subtype_val, ?_, ?_⟩
  · have key : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J,
        ((x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) : GL (Fin n) _) ∈ Set.range f :=
      fun x => MonoidHom.mem_range.mp x.2
    refine Function.Injective.countable
      (f := fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J => (⟨_, key x⟩ : Set.range f)) ?_
    intro x y h
    have h0 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h0)
  · intro g h
    rfl
  · intro Ω hΩ
    obtain ⟨C, hC⟩ := (hΩ.image (continuous_ht σ J)).bddAbove
    exact ⟨C, fun g hg => hC ⟨g, hg, rfl⟩⟩

end PositivityTheory.ThKEst

end
