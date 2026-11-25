module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul

@[expose] public section

noncomputable section

namespace MassDataMassesW

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.BasicNotions

theorem continuous_splitA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous (splitA σ J) := by
  haveI : IsModuleTopology (AF F) (TensorProduct F (AF F) E) := ⟨rfl⟩
  have hha {R' : Type} [CommRing R'] [Algebra F R'] [TopologicalSpace R']
      {g : AF F →ₐ[F] R'} (hg : Continuous g) : Continuous (haMap σ J g) := by
    haveI : IsModuleTopology R' (TensorProduct F R' E) := ⟨rfl⟩
    haveI : ContinuousAdd (TensorProduct F R' E) := IsModuleTopology.toContinuousAdd R' _
    haveI : ContinuousSMul R' (TensorProduct F R' E) := IsModuleTopology.toContinuousSMul R' _
    let f : TensorProduct F (AF F) E →ₛₗ[g.toRingHom] TensorProduct F R' E :=
      { toFun := tensMap (E := E) g
        map_add' := map_add _
        map_smul' := fun a x => by rw [Algebra.smul_def, Algebra.smul_def, map_mul]; congr 1 }
    have hφ := IsModuleTopology.continuous_of_linearMapₛₗ hg f
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    exact ⟨(Units.continuous_val.comp continuous_subtype_val).matrix_map hφ,
      (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map hφ⟩
  unfold splitA
  rw [MonoidHom.coe_prod]
  exact Continuous.prodMk (hha continuous_fst) (hha continuous_snd)

theorem continuous_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : Continuous (X.toInf hb) := by
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.toInf
  exact continuous_fst.comp ((continuous_splitA _ _).comp
    ((Formalism.L2.SG.AdBridge.toHA X.B.I hb).continuous.comp (continuous_id.prodMk continuous_const)))

theorem measurable_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : Measurable (X.toInf hb) := by
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_toInf X hb).measurable

theorem volHTie_holds : VolHTie := by
  intro D X hb u hMT
  have h := (hMT.2.2.2 u).2
  have h1 := congrArg (fun m => m Set.univ) h
  rw [Measure.map_apply (measurable_toInf X hb) MeasurableSet.univ, Set.preimage_univ] at h1
  rw [← h1]
  unfold Formalism.L2.SG.Measures.amb
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]

end MassDataMassesW
