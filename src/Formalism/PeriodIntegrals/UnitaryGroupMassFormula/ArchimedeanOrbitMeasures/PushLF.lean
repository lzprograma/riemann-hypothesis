module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Matrix

export PI.VolStabSW.TensAllW (LIP lip_field lip_pi inj_of_isUnit wMat wMat_mulVec wMat_mulVec_eq_zero
  linIndep_iff continuous_wMat isOpen_linIndep)
export PI.VolStabS.PositiveNearLattice (crd continuous_crd)
export PI.VolStabSW (lip_ainf)

theorem isOpen_units_Ainf (F : Type) [Field F] [NumberField F] : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  show IsOpen {y : (v : InfinitePlace F) → v.Completion | IsUnit y}
  have : {y : (v : InfinitePlace F) → v.Completion | IsUnit y} =
      ⋂ v, (fun y : (v : InfinitePlace F) → v.Completion => y v) ⁻¹' {z | z ≠ 0} := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage]
    show IsUnit y ↔ ∀ v, y v ≠ 0
    rw [Pi.isUnit_iff]; simp only [isUnit_iff_ne_zero]
  rw [this]; exact isOpen_iInter_of_finite fun v => isOpen_ne.preimage (continuous_apply v)

theorem isOpen_IndI {D : D7} (X : HidaSetting D) : IsOpen (IndI X) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact isOpen_linIndep (Module.finBasis X.B.I.F X.B.I.E) (Ainf X.B.I.F) (isOpen_units_Ainf _) (lip_ainf _)

section LC

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

instance locallyCompactSpace_tensP : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tensP (F := F) (E := E) R
  exact h.isClosedEmbedding.locallyCompactSpace

instance t2Space_tensorProduct : T2Space (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tensP (F := F) (E := E) R
  exact h.isEmbedding.t2Space

end LC

instance t2Space_infiniteAdeleRing_archimedean_orbit_measures (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem lfFib_holds : LFFib := by
  intro D X u' ψ hT μinf νinf fibInf hP K hK hKU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, -, hkcl, hKk, hkU⟩ := exists_compact_closed_between hK (isOpen_IndI X) hKU
  obtain ⟨f, hf1, hf0, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hKk)
  have hts : tsupport f ⊆ IndI X := by
    refine (closure_minimal ?_ hkcl).trans hkU
    intro y hy
    by_contra h
    exact hy (hf0 (fun h' => h (interior_subset h')))
  have hI := ((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 (TI X u' hT) (Set.mem_univ _)
  calc fibInf (TI X u' hT) K ≤ fibInf (TI X u' hT) {y | 1 ≤ ENNReal.ofReal (f y)} :=
        measure_mono fun y hy => by
          simp only [Set.mem_ofPred_eq]
          rw [hf1 hy]
          simp
    _ = 1 * fibInf (TI X u' hT) {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf (TI X u' hT)) :=
        mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1
    _ < ⊤ := hI.lintegral_lt_top

end PI.AprimeInfW
