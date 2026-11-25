module

public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem nonempty_ix_of_pos : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3), A3.fam3.Ok3 s → Zs.InBlock → (A3.side3 P ψ Zs).Pos → Nonempty A3.fam3.base3.Ix := by
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 P ψ Zs hOk hin hpos
  by_contra hne
  have hfalse : ∀ x, ¬ A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id x := by
    rintro x ⟨p, hp, -⟩
    exact hne ⟨⟨p, hp⟩⟩
  have hsame := A3.fam3.sameTypes_base3 hOk P ψ hin
  have hbot : Formalism.L2.Col.eigSum (A3.fam3.RI A3.fam3.F.μ0).opAll
      (A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id) = ⊥ := by
    unfold Formalism.L2.Col.eigSum
    simp [hfalse]
  rw [hbot, BlockDat.good_part_coordinates_bot, le_bot_iff] at hsame
  unfold FamIn3.side3 DefFam3.side3 DefSide.Pos at hpos
  simp only [BlockDat.dZ, subDim] at hpos
  rw [hsame] at hpos
  simp at hpos

end GlobalTheory.Div
