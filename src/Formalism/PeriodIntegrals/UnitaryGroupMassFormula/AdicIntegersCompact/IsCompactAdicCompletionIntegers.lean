module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Topology.Algebra.Valued.LocallyCompact

@[expose] public section

namespace PI.IntAdCpctOpenWork

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_algebraMap (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem denseRange : DenseRange (algebraMap F (v.adicCompletion F)) := by
  exact denseRange_algebraMap F v

theorem exists_close (x : v.adicCompletion F) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  apply PI.WAU.exists_int_near <;> assumption

theorem mem_maximalIdeal_iff (x : Valued.integer (v.adicCompletion F)) :
    x ∈ IsLocalRing.maximalIdeal (Valued.integer (v.adicCompletion F)) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  show ¬IsUnit x ↔ _
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

noncomputable def toInt : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    (Valued.integer (v.adicCompletion F)) (fun a => by
      show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ≤ 1
      rw [valued_algebraMap]
      exact valuation_le_one v a)

noncomputable def resHom :
    𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
  (IsLocalRing.residue _).comp (toInt v)

theorem resHom_surjective : Function.Surjective (resHom v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := exists_close v x x.2
  refine ⟨a, ?_⟩
  unfold resHom
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  have e : ((toInt v a - x : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) - x := rfl
  rw [e, Valuation.map_sub_swap]
  exact ha

theorem resHom_eq_zero (a : 𝓞 F) (ha : a ∈ v.asIdeal) : resHom v a = 0 := by
  unfold resHom
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1
  rw [valued_algebraMap]
  exact (valuation_lt_one_iff_mem v a).mpr ha

theorem finite_residueField : Finite (Valued.ResidueField (v.adicCompletion F)) := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let g := Ideal.Quotient.lift v.asIdeal (resHom v) (fun a ha => resHom_eq_zero v a ha)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := resHom_surjective v y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  exact Finite.of_surjective g hg

theorem compactSpace_integer : CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residueField v⟩
  · exact ((Valued.v.integer.toAddSubgroup).isClosed_of_isOpen (Valued.isOpen_integer _)).completeSpace_coe
  · exact (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F))

theorem isCompact_adicCompletionIntegers :
    IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  haveI := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

instance compactSpace_set : CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

instance compactSpace_sub : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

theorem main : Formalism.L2.Props.IntAdelesCompactOpen := by
  intro F _ _
  have hO : ∀ w : HeightOneSpectrum (𝓞 F),
      IsOpen ((w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    fun w => Valued.isOpen_valuationSubring _
  refine ⟨RestrictedProduct.isOpen_forall_mem hO, ?_⟩
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap hO).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end PI.IntAdCpctOpenWork
