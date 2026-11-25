module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.Topology.Algebra.MvPolynomial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct


theorem UpperTheory.V.Hi.levelUR2GalRes :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (G : Type) [Group G] [TopologicalSpace G] (n : ℕ) (r : G →* GL (Fin n) (Qbar l)), Continuous r → ∀ φ : G → (ResidueField c.O)[X], IsLocallyConstant φ → ∀ S : Set G, Dense S → (∀ g ∈ S, ∀ (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1) → ∀ g (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1 := by
  intro l _ c G _ _ n r hr φ hφ S hS hSb g i b hb
  have hc : Continuous fun h : G => (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
    (_root_.GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix n i).comp (Units.continuous_val.comp hr)
  have hU : IsOpen {h : G | φ h = φ g} := hφ.isOpen_fiber _
  have hW : IsOpen {h : G | ‖(r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
      (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i‖ < 1} :=
    isOpen_lt (continuous_norm.comp (hc.sub continuous_const)) continuous_const
  obtain ⟨h, ⟨hh1, hh2⟩, hhS⟩ := hS.inter_open_nonempty _ (hU.inter hW) ⟨g, rfl, by simp⟩
  have key := hSb h hhS i b (by rw [hb, Set.mem_setOf_eq.mp hh1])
  have hh2' := Set.mem_setOf_eq.mp hh2
  rw [norm_sub_rev] at hh2'
  calc ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖
      = ‖((r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i) +
        ((r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          algebraMap c.O (Qbar l) b)‖ := by congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ < 1 := max_lt hh2' key
