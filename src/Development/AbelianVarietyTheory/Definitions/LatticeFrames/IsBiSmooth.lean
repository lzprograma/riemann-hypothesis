module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct

namespace GlobalTheory.SeeSaw

variable {D : D7}

def IsBiSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

structure IsBiTheta (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  smooth : IsBiSmooth C
  quasiL : ∀ γ u v, C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v
  quasiR : ∀ γ u v, C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v
  levL : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v
  levR : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u

def BiAct (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'),
    IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C →
      (∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u) ∧
      (∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v) ∧
      (∀ p q u v, omb q (fun v' => oma p (fun u' => C u' v') u) v = oma p (fun u' => omb q (C u') v) u) ∧
      Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
        omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

end Dat

end GlobalTheory.SeeSaw

end
