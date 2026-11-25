module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesPropertiesStatement
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace Gp91

namespace GlobalTheory.CWDeriv

theorem hInvol (k r : ℕ) : AAInvW.HInvol (Formalism.QuantumDeterminants.Hpk k r) :=
  _root_.GlobalTheory.CWDeriv.hInvol k r

theorem sm_comb {k r : ℕ} {R : Rep k r} (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    a • (x - y) - z ∈ R.sm :=
  _root_.GlobalTheory.CWDeriv.sm_comb a hx hy hz

end GlobalTheory.CWDeriv

namespace GlobalTheory

theorem cwCont_continuousOn_hasDerivAt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ v ∈ R.sm, ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → HasDerivAt (fun t : ℝ => Bm (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) (Bm (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) 0 := by
  intro hK k r ε mu R hR
  exact _root_.GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε mu R (_root_.GlobalTheory.isDS_of_isDG hR)

end GlobalTheory

end Gp91
