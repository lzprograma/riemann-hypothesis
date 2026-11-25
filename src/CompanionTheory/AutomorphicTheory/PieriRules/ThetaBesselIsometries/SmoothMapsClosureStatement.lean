module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace Gp91

namespace GlobalTheory.SmMapAct

theorem smMap_act : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  intro hK k r ε mu mu' mu'' R R' R'' hR hR' hR''
  exact _root_.GlobalTheory.SmMapAct.smMap_act hK k r ε mu mu' mu'' R R' R''
    (_root_.GlobalTheory.isDS_of_isDG hR) (_root_.GlobalTheory.isDS_of_isDG hR') (_root_.GlobalTheory.isDS_of_isDG hR'')

end GlobalTheory.SmMapAct

theorem _root_.Gp91.GlobalTheory.T.smooth_maps_closure : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) :=
  @GlobalTheory.SmMapAct.smMap_act

end Gp91
