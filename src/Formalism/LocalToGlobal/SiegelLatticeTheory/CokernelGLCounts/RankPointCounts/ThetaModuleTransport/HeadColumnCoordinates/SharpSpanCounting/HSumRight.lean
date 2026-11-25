module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.SharpEquivApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section General

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_right {ι : Type} (s : Finset ι) (c : ι → E) (g : ι → V) (u : V) :
    H.h u (∑ i ∈ s, c i • g i) = ∑ i ∈ s, M.L.cj (c i) * H.h u (g i) := by

  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem span_eq_sum (g : ι → V) (hG : IsUnit (gramH H g).det) (u : V)
    (hu : u ∈ Submodule.span E (Set.range g)) :
    u = ∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i := by
  have hs : (∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i) ∈
      Submodule.span E (Set.range g) :=
    (Submodule.mem_span_range_iff_exists_fun E).2 ⟨_, rfl⟩
  have h' : pairSpan H g ⟨u, hu⟩ = pairSpan H g ⟨_, hs⟩ := by
    show pairing H g u = pairing H g (∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i)
    rw [pairing_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
    rfl
  exact congrArg Subtype.val ((pairSpan_bij H g hG).1 h')

theorem h_eq_form (g : ι → V) (hG : IsUnit (gramH H g).det) (u w : V)
    (hu : u ∈ Submodule.span E (Set.range g)) :
    H.h u w = ∑ i, ∑ j, H.h u (g i) * (gramH H g)⁻¹ i j * M.L.cj (H.h w (g j)) := by
  refine (congrArg (fun x => H.h x w) (span_eq_sum H g hG u hu)).trans ?_
  rw [h_sum_left]
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [H.h_herm w (g j)]

end General

end Formalism.L2.SG.LocalCountModules.LocCntCommon
