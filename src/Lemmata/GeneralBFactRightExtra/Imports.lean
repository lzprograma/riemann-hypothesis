module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
import Lemmata.GeneralBFactUpper.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe

@[expose] public section

namespace Bl.general_b_fact_right'''

theorem goal1 :
  ∀ {K : Type} [NormedField.{0} K] [IsUltrametricDist.{0} K] {p : Nat} {a b : K},
  LE.le.{0} (Norm.norm.{0} a) 1 →
    LE.le.{0} (Norm.norm.{0} b) 1 →
      LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) (Inv.inv.{0} (Nat.cast.{0} p)) →
        ∀ (k : Nat),
          LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} a k) (HPow.hPow.{0, 0, 0} b k)))
            (Inv.inv.{0} (Nat.cast.{0} p)) := by
  intro K _ _ p a b ha hb hab k
  exact (GlobalTheory.NormEvalSubBound.norm_pow_sub_pow_le ha hb k).trans hab

end Bl.general_b_fact_right'''
