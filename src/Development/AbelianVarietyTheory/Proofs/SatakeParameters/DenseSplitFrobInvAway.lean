module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.Topology.Algebra.MvPolynomial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.SplitAttUniq

theorem repIso_of_dense {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
    (r r' : G E Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (D : Set (G E Ω)) (hD : Dense D)
    (he : ∀ g ∈ D, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    UpperTheory.V.Af.RepIso r r' := by
  have hcp : ∀ g : G E Ω, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (_root_.GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix a i).comp (Units.continuous_val.comp hc)
    have h2 : Continuous fun g : G E Ω => (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (_root_.GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix a i).comp (Units.continuous_val.comp hc')
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    intro σ hσ
    simp only [he σ hσ]
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' hcp
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.SplitAttUniq
