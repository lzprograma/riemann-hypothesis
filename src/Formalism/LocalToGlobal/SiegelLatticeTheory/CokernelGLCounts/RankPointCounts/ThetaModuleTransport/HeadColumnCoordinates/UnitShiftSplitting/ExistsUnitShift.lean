module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integral
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem e_alg (g : SplitG M.L) (s : F) : g.e (algebraMap F E s) = (s, s) := by
  rw [AlgEquiv.commutes]
  rfl

theorem comp_mem_O (g : SplitG M.L) {x : E} (hx : x ∈ M.L.O) :
    (g.e x).1 ∈ 𝒪[F] ∧ (g.e x).2 ∈ 𝒪[F] := by
  have hxI : IsIntegral 𝒪[F] x := (M.L.O_def x).mp hx
  have key : ∀ f : E →ₐ[F] F, f x ∈ 𝒪[F] := fun f =>
    (Valuation.integer.integers (valuation F)).mem_of_integral (hxI.map (f.restrictScalars 𝒪[F]))
  exact ⟨key ((AlgHom.fst F F F).comp g.e.toAlgHom), key ((AlgHom.snd F F F).comp g.e.toAlgHom)⟩

theorem isUnit_of_comp (g : SplitG M.L) {y : E} (h1 : (g.e y).1 ≠ 0) (h2 : (g.e y).2 ≠ 0) : IsUnit y := by
  have hu : IsUnit (g.e y) := Prod.isUnit_iff.mpr ⟨h1.isUnit, h2.isUnit⟩
  exact (isUnit_map_iff g.e y).mp hu

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
