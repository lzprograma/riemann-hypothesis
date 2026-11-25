module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def IsUnimodularLC (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ LocallyCompactSpace G ∧ SecondCountableTopology G ∧
    BorelSpace G ∧ (∃ μ : Measure G, μ.IsHaarMeasure) ∧
    ∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant

def IsDiscreteWithDomains {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (Γ : Subgroup G) : Prop :=
  Countable Γ ∧ DiscreteTopology Γ ∧
    ∀ μ : Measure G, μ.IsHaarMeasure →
      ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ IsFundamentalDomain Γ 𝓕 μ

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratPts (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ J) := HFinIn R σ J

def UnimodularOver (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  IsUnimodularLC (HA R σ J) ∧
    ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsUnimodularLC (Hstab R σ J x)

end Points

theorem isUnimodularLC_of_commGroup (G : Type) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] : IsUnimodularLC G :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun _ _ => inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
