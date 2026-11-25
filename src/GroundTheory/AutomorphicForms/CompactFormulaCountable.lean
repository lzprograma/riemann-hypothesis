module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField IsDedekindDomain Topology Filter TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

variable (K : Type*) [Field K] [NumberField K]

instance secondCountableTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have : SeparableSpace (v.adicCompletion K) :=
    ⟨⟨Set.range (algebraMap K _), Set.countable_range _,
      HeightOneSpectrum.denseRange_algebraMap K v⟩⟩
  exact UniformSpace.secondCountable_of_separable _

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  let R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K
  let A := fun v : HeightOneSpectrum (𝓞 K) =>
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hAo : ∀ v, IsOpen (A v) := fun v => GroundTheory.Global.isOpen_adicCompletionIntegers v
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
      cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) := fun S => by
    rw [le_principal_iff]
    exact S.finite_toSet.compl_mem_cofinite
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (Πʳ v, [R v, A v]) :=
    fun S => Set.range (RestrictedProduct.inclusion R A (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo (hS S)).isOpen_range
  have hSC : ∀ S, SecondCountableTopology (U S) := fun S => by
    have h1 :
        SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    have hfin : {v | x.1 v ∉ A v}.Finite := x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    show ∀ᶠ v in 𝓟 ((hfin.toFinset : Set (HeightOneSpectrum (𝓞 K)))ᶜ), x.1 v ∈ A v
    rw [eventually_principal]
    intro v hv
    by_contra h
    exact hv (by simpa using h)
  show SecondCountableTopology (Πʳ v, [R v, A v])
  exact @secondCountableTopology_of_countable_cover _ _ _ _ _ hSC hUo hcov

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

end GroundTheory.Automorphic
