module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf

theorem trExistsC_of (hP : ∀ (D : D7) (X : HidaSetting D), SatGram.PsiCond X) : TRExistsC :=
  fun D X _ => SatGram.typedRed_exists' SatGramLoc.split_prime_local_holds SatGramLoc.reduction_structure_holds (hP D X)

theorem psiCond_holds {D : D7} (X : HidaSetting D) : SatGram.PsiCond X :=
  open Formalism.L2.SG.Pf.SatGram in
  psi_conductor_all_places D X

theorem trExistsC_holds : TRExistsC :=
  trExistsC_of (fun _ X => psiCond_holds X)

section

variable {D : D7} (X : HidaSetting D)

theorem typed_count_holds (TR : TypedRed X) (i : Fin 2) :
    Fintype.card {v : TR.Pl // Fintype.card (TR.Fq v) = D.host.g i} = Module.finrank ℚ X.B.I.F :=
  open Formalism.L2.SG.Pf.SatGram Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.GGMirabolic in
  typed_count (redExists_holds X) (gUnif_holds X) (gResCard_holds X) (gCount_of splitPrimeLoc_holds) TR i

theorem tt_eq_holds (TR : TypedRed X) :
    ∏ v, (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) =
      (1 + 3 / (D.host.g 0 : ℝ)) ^ Module.finrank ℚ X.B.I.F * (1 + 3 / (D.host.g 1 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
  exact SatGram.tt_eq (redExists_holds X) (gUnif_holds X) (gResCard_holds X)
    (SatGram.gCount_of splitPrimeLoc_holds) TR

theorem gamma_one_typed_places_holds (TR : TypedRed X) :
    Gam1 TR = ∏ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
      (Formalism.L2.SG.TypedSets.glkC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) /
        (Formalism.L2.SG.TypedSets.ukC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) :=
  open Formalism.L2.SG.Pf.SatGram Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.GGMirabolic in
  gamma_one_eq_prod_typed_places (redExists_holds X) (gUnif_holds X) (gResCard_holds X) (gCount_of splitPrimeLoc_holds) TR

theorem gSplitX_holds : Formalism.L2.SG.LocVol.GSplitX X := by
  intro p
  have hg0 : D.host.g 0 ≠ 0 := (D.host.g_prime 0).ne_zero
  have hg1 : D.host.g 1 ≠ 0 := (D.host.g_prime 1).ne_zero
  have hty := (Formalism.L2.SG.TypedSets.mem_typSet X.B.I.F _ _ hg0 hg1 p.1).1 p.2
  have hg : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    rw [X.g_eq, Nat.cast_mul]
    rcases hty with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h
  refine ⟨?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    unfold Formalism.L2.SG.LocVol.gAt
    split_ifs with h0
    · exact gResCard_holds X p.1 0 h0
    · exact gResCard_holds X p.1 1 (hty.resolve_left h0)
  · unfold Formalism.L2.SG.LocVol.etaV
    rw [ite_eq_left (split_at_g X p.1 hg)]

end

end Formalism.L2.SG.Pf
