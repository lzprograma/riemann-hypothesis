module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacter

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ n ∈ flagN B.d, flatFB s (s.om (1, n) Ψ) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s Ψ := by
  first | exact @GlobalTheory.Unf.FB.UnipAct.flatFB_flagN
