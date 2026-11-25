module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.Ring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe

@[expose] public section

namespace Bl.general_b_fact_upper

theorem goal1 :
  ∀ {K : Type} [NormedField.{0} K] [IsUltrametricDist.{0} K] {x y : K},
  LE.le.{0} (Norm.norm.{0} x) 1 →
    LE.le.{0} (Norm.norm.{0} y) 1 →
      ∀ (n : Nat),
        LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} x n) (HPow.hPow.{0, 0, 0} y n)))
          (Norm.norm.{0} (HSub.hSub.{0, 0, 0} x y)) :=
  GlobalTheory.NormEvalSubBound.norm_pow_sub_pow_le

end Bl.general_b_fact_upper
