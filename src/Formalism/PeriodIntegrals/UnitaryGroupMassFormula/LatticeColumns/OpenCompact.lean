module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxTop
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

def FinHAHomeo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I), ∃ e : I.Gf ≃ₜ* HA (Af I.F) I.cm.sig I.J,
    ∀ x, e x = (splitA I.cm.sig I.J (toHA I hb (1, x))).2

def LevelOpenCompact : Prop := ∀ {D : D7} (X : HidaSetting D), IsOpen X.K2 ∧ IsCompact X.K2

def KsetCompactAll : Prop := ∀ I : Formalism.MainNotions.S.AutInst, IsCompact I.Kset

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosed_stabT_Af {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT (Af F) σ J X0 : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) := by
  apply _root_.PI.LevelKSplit.W.ExC.isClosed_stabT <;> assumption

end Gen

theorem finHA_mem_Kf_iff {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔ x ∈ X.B.I.Kset := by
  have hK := adelic_compact_finite_places X.B.I (toHA X.B.I hb (1, x))
  have hbr : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := (toHA_isBridge X.B.I hb (1, x)).2
  rw [← hbr] at hK
  rw [Kf, Subgroup.mem_iInf]
  constructor
  · intro h
    exact hK.2 h
  · intro h
    exact hK.1 h

theorem kf_eq_image {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)
    (hs : Function.Surjective (finHA X hb)) :
    (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) = finHA X hb '' X.B.I.Kset := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨x, (finHA_mem_Kf_iff X hb x).1 hz, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (finHA_mem_Kf_iff X hb x).2 hx

theorem openCompactStep_of (hE : FinHAHomeo) (hK2 : LevelOpenCompact) (hKc : KsetCompactAll) :
    OpenCompactStep := by
  intro D X hb hK u _hT _hL
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := isTopGroup_HA (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.sig X.B.I.J
  obtain ⟨e, he⟩ := hE X.B.I hb
  have hfe : (finHA X hb : X.B.I.Gf → HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) = e := by
    funext x
    exact (he x).symm
  constructor
  ·
    have hset : (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
        Subtype.val ⁻¹' K2u X hb u := by
      unfold unitaryLevelClosureSubgroup
      have : (Subtype.val ⁻¹' K2u X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
          (unitaryLevelIntersection X hb hK u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := rfl
      rw [this, Subgroup.closure_eq]
    rw [hset]
    refine IsOpen.preimage continuous_subtype_val ?_
    have h1 : IsOpen (levelUnitary X hb) := by
      unfold levelUnitary
      rw [hfe]
      exact e.toHomeomorph.isOpenMap _ (hK2 X).1
    set a := finHA X hb (X.xu u)
    have hc : K2u X hb u = ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)) '' levelUnitary X hb := rfl
    rw [hc]
    exact ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)).isOpenMap _ h1
  ·
    have hsurj : Function.Surjective (finHA X hb) := by
      rw [hfe]
      exact e.surjective
    have hKf : IsCompact (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
        Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
      rw [kf_eq_image X hb hsurj, hfe]
      exact (hKc X.B.I).image e.continuous
    have hH : IsClosed ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
        Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
      isClosed_stabT_Af X.B.I.cm.sig X.B.I.J (tupH (frameOf X u))
    rw [Subtype.isCompact_iff]
    have : ((↑) : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) → HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ''
        (KHg X u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∩
          (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
            Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
      ext z
      simp only [Set.mem_image, SetLike.mem_coe, Set.mem_inter_iff, KHg, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨z, h1⟩, h2, rfl⟩
    rw [this]
    exact hKf.inter_left hH

end PIW.MassDataColumns
