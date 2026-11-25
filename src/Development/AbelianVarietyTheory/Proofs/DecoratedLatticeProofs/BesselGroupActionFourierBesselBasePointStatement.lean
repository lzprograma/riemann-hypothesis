module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePoint

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), x0 B ⬝ a = x0 B ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  first | exact @GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint
