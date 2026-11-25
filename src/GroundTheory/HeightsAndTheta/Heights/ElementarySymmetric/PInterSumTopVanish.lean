module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterSumTopVanish
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumAdditive

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter
noncomputable section
universe u w
attribute [local instance] twistMonoid

theorem InterSumTopVanish.proof (hM : MixedTwistShift.Statement.{u, w}) : InterSumTopVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L hW
  classical
  let L₀ : Fin n → LineBundle k x := fun j => L (Fin.castSucc j)
  let shift := hM k Ω N x n pp hW.isPrime hW.homog hW.le hW.dim.le L₀
  filter_upwards [shift (L (Fin.last n)) 0, shift (twistBundle k x 0) 0] with c hA hB
  rw [interSum_eq_mixDiff, show (fun i => (L i).toSubSystem) =
      Fin.snoc (α := fun _ => SubSystem k x Ω) (fun j => (L₀ j).toSubSystem)
        (L (Fin.last n)).toSubSystem from by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [L₀], mixDiff_snoc]
  refine sub_eq_zero.mpr (Eq.trans ?_ ((hA.trans hB.symm).trans ?_))
  all_goals
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tensorSub_eq_prod, add_zero]
    apply congrArg (fun F : SubSystem k x Ω =>
      (-1 : ℤ) ^ (n - T.card) * restrLen pp (F.twist (twistSys k x (c : ℤ))))
  · exact SubSystem.twist_comm _ _
  · exact SubSystem.twist_twistSys_zero _

end
end GroundTheory.Heights₂.Heights.Kleiman
