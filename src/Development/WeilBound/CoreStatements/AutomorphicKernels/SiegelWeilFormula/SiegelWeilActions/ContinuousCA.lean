module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.AddFDOfCover
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InclRSmul
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import GroundTheory.GlobalFields.Adele.Approximation
import Mathlib.Tactic.Linter.HaveILetI
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.VaddInvBotProd

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

scoped instance afSC : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
scoped instance afBorel : BorelSpace (AF F) := ⟨rfl⟩

variable (F) in
def lamA : Measure (AF F) := Measure.addHaar

instance lamA_haar : (lamA F).IsAddHaarMeasure := by unfold lamA; infer_instance

variable (F) in
def fA : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup

instance countable_fA : Countable (fA F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have h : ((fA F : AddSubgroup (AF F)) : Set (AF F)).Countable := by
    refine (Set.countable_range (algebraMap F (AF F))).mono fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, rfl⟩
  exact h.to_subtype

theorem exists_fd_fA : ∃ 𝓐 : Set (AF F), IsAddFundamentalDomain (fA F) 𝓐 (lamA F) ∧ lamA F 𝓐 ≠ 0 ∧ lamA F 𝓐 ≠ ⊤ := by
  haveI : DiscreteTopology (fA F) := by
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨O, hOU, hO, h0⟩ := mem_nhds_iff.1 hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    convert hO.preimage continuous_subtype_val using 1
    ext ⟨x, hx⟩
    constructor
    · intro h
      have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
      subst h1
      exact h0
    · intro h
      obtain ⟨y, rfl⟩ := hx
      have hy : y = 0 := hU0 y (hOU h)
      subst hy
      exact Set.mem_singleton_iff.2 (Subtype.ext (map_zero _))
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  obtain ⟨𝓐, h𝓐, hc⟩ := ComplexParameterFamilyContinuity.addFD_of_cover' (fA F) hK (fun x => by
    obtain ⟨y, hy⟩ := hKx x
    exact ⟨-algebraMap F (AF F) y, ⟨-y, map_neg _ _⟩, by rwa [neg_add_eq_sub]⟩) (lamA F)
  refine ⟨𝓐, h𝓐, h𝓐.measure_ne_zero (NeZero.ne _), ?_⟩
  exact ne_top_of_le_ne_top hc.measure_lt_top.ne (measure_mono subset_closure)

variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem isClosed_nA' {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := hb.1
  have h : (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := by
    ext β
    exact kunf.mem_nA_iff hε β
  rw [h]
  have hc : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => β.map (cA σ) :=
    continuous_id.matrix_map (_root_.GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA (σ := σ))
  exact isClosed_eq continuous_id.matrix_transpose (hc.const_smul (((ε : ℤ) : AE F E))).neg

instance lcNA {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} [Fact (IsFrame2 σ Y b)] :
    LocallyCompactSpace (nA σ Y b) :=
  (isClosed_nA' (Fact.out : IsFrame2 σ Y b)).isClosedEmbedding_subtypeVal.locallyCompactSpace

end PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C5

theorem shear_mp' {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [AddGroup Y] [MeasurableAdd₂ Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant] (s : X → Y) (hs : Measurable s) :
    MeasurePreserving (fun p : X × Y => (p.1, p.2 + s p.1)) (μ.prod ν) (μ.prod ν) :=
  (MeasurePreserving.id μ).skew_product (g := fun x y => y + s x) (measurable_snd.add (hs.comp measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self ν (s x))

open scoped Pointwise in
theorem fd_prod {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableAdd X] [MeasurableAdd Y] {Γ : AddSubgroup X} {Δ : AddSubgroup Y} [Countable Γ] [Countable Δ]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant] [ν.IsAddRightInvariant] {s : Set X} {t : Set Y}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.fd_prod' <;> assumption

end PositivityTheory.SiegelWeilFormula.Act.C5

end
