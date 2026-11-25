module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.NX
open scoped TensorProduct
open Classical

namespace GlobalTheory.TowerCov

variable {D : D7}

def IsLevN (E : ExpSet D) (N : ℕ) : Prop :=
  N ≠ 0 ∧ (∀ p : ℕ, p.Prime → p ∣ N →
    p ≠ 2 ∧ Nat.Coprime p E.l ∧ (∀ a, p ≠ E.pde a) ∧ (∀ a, p ≠ E.gp a) ∧ D.host.cls p = .splitK ∧
      ¬ p ∣ Ideal.absNorm D.host.ccK) ∧ Squarefree N

def LevN (E : ExpSet D) : Type := {N : ℕ // IsLevN E N}

section Covers

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.CoverRead

variable {E : ExpSet D} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (hV : T.V j σ = E.W)
  (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (z : ℂ)

def placesIn {L : Type} [Field L] [NumberField L] (ι : L →+* ℂ) (Λ : Subring ℂ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {la | ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ}

end Covers

end GlobalTheory.TowerCov
