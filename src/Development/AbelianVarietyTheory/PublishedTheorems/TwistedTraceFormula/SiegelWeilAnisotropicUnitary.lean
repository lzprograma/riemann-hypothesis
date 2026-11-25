module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

namespace GlobalTheory.ThetaMean

variable {D : D7} {A B : HSp D}

def thetaMean {S T : HSp D} (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D T))
    (f : WO S T → ℂ) : GA D S → ℂ :=
  fun g => ⨍ q, AutomorphicL2Unitary.descend (GQ T) (fun h => thetaKO ω g h f) q ∂autMeasure T ν

theorem lagr_add (z z' : WO A B) : lagr A B (z + z') = lagr A B z + lagr A B z' := Matrix.ext fun i k => by
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
    simp only [Matrix.add_apply, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_add]

theorem lagr_rat (γ : Matrix (Fin B.rank) (Fin A.rank) D.host.E) :
    lagr A B (rat γ) = ratW B (dblSp A) (Matrix.of fun i => pairVec finSumFinEquiv (γ i) (-(γ i))) :=
  Matrix.ext fun i k => by
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
      simp only [lagr, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, ratW, rat, Matrix.of_apply,
        Matrix.map_apply, pairVec_inl, pairVec_inr, Pi.neg_apply,
        map_neg]

theorem continuous_lagr : Continuous (lagr A B) := continuous_matrix fun i k => by
  obtain ⟨i1, -⟩ := lattice_Mx D B.rank A.rank
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    exact continuous_id.matrix_elem i j
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    exact (continuous_neg (G := WO A B)).matrix_elem i j

theorem hO_lagr (z z' : WO A B) : hO (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, lagr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg, neg_zero,
    Finset.sum_neg_distrib, add_neg_cancel]

theorem symplOH_lagr (z z' : WO A B) : symplOH (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  rw [symplOH, symplO, hO_lagr, mul_zero, map_zero, mul_zero]

variable {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}

section Zero

variable {f : WO (dblSp A) B → ℂ} {μ μ' : Measure (WO A B)} {𝓨 𝓨' : Set (WO A B)}
  {ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)}

theorem periodic_lagr (hf : IsThetaFunO ψ (dblSp A) B f) :
    ∀ γ ∈ ratMx D B.rank A.rank, ∀ z, f (lagr A B (γ + z)) = f (lagr A B z) := by
  rintro _ ⟨γ, rfl⟩ z
  change f (lagr A B (rat γ + z)) = _
  rw [lagr_add, lagr_rat, hf.quasi, ← lagr_rat, symplOH_lagr, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrableOn_lagr (hμ : IsCovolOne (ratL B A) μ 𝓨) (hf : IsThetaFunO ψ (dblSp A) B f) :
    IntegrableOn (fun z => f (lagr A B z)) 𝓨 μ :=
  covolOne_integrableOn hμ _ (hf.cont.comp continuous_lagr) (periodic_lagr hf)

end Zero

variable {S T : HSp D} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}
  (hω : IsWeilDatumO ψ S T χ χ' ω) (hf : IsThetaFunO ψ S T f)
include hω hf

theorem leftInv_theta (g : GA D S) : LeftInv (GQ T) fun h => thetaKO ω g h f := fun γ hγ h => by
  have := hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres (g, h) f hf)
  rwa [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at this

variable {ν : Measure (GA D T)} [ν.IsHaarMeasure]

end GlobalTheory.ThetaMean

namespace GlobalTheory.Published

open GlobalTheory.ThetaMean

def SiegelWeilAnisotropicUnitary : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 1 ≤ B.rank → IsAniso B →
  ∀ (χB : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χB ω →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) →
  ∀ (μ : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) μ 𝓨 →
  ∀ ν : Measure (GA D B), ν.IsHaarMeasure →
  ∀ f : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B f → IsKFinVec ω (Khat A a) f →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B ν)) ∧
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B)
      ((if A.rank < B.rank then 1 else 2 : ℂ) • thetaMean ω ν f)

end GlobalTheory.Published

end
