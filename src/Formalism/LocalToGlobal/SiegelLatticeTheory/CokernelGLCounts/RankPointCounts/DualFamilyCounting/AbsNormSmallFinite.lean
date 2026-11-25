module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqOfCover
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal

@[expose] public section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

theorem absNorm_small_finite (D : Formalism.BasicNotions.D7) :
    {p : PlF D | (Ideal.absNorm p.asIdeal : ℝ) < 3}.Finite := by
  refine (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
    (S := 𝓞 D.host.F) 2).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  have h : Ideal.absNorm p.asIdeal < 3 := by exact_mod_cast hp
  exact Nat.lt_succ_iff.mp h

end Formalism.L2.SG.Pf.Cnt
