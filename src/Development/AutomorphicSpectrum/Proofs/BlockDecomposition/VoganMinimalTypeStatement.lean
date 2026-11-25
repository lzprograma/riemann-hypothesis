module

public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepFormulaF
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

@[expose] public section

namespace GlobalTheory.CompanionTheory.DiscreteSeries

open GlobalTheory.LowestKTypeDetermines in
theorem stepVogan : PositivityTheory.RgDs.Hilb.StepVogan := by
  intro n ε lam η hlam hη
  obtain ⟨c, hc, rfl⟩ := hη
  have hk : ReciprocityTheory.ChartRestriction.DS.lowK ε lam =
      Formalism.QuantumDeterminants.lowK ε lam := rfl
  unfold Formalism.MainNotions.S.vNormSq
  rw [hk, add_right_comm, lowK_add]
  have := nsq_add_cone (strictAnti_add_rho hlam.1).antitone hc
  linarith [nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b)]

end GlobalTheory.CompanionTheory.DiscreteSeries
