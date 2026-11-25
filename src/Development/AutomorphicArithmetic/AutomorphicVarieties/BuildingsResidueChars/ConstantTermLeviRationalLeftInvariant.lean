module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockDiagConjUnipotentLinear
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralUnipFundamentalDomainCompLatticePreservi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct

private theorem blk_mul_blk_inv {r s : ℕ} {R : Type} [CommRing R] (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R) :
    blk m₁ m₂ * blk m₁⁻¹ m₂⁻¹ = 1 := by
  simp only [blk]
  rw [emb_comm m₁⁻¹ m₂⁻¹, map_inv, map_inv]
  group

theorem UpperTheory.constantTerm_levi_rational_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (φ : AdelicGLn.AdelicGL K (r + s) → ℂ),
      IsLeftInvariant φ → ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g,
        constantTerm (r := r) φ (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) =
          constantTerm (r := r) φ g := by
  intro K _ _ r s φ hφ γ₁ γ₂ g
  have hdiag : ∀ γ : GL (Fin (r + s)) K, AdelicGLn.diagonal K (r + s) γ =
      GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ := fun _ => rfl
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁ γ₂
  obtain ⟨c', hc'⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁⁻¹ γ₂⁻¹
  have hDD : AdelicGLn.diagonal K (r + s) (blk γ₁⁻¹ γ₂⁻¹) = (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    rw [← map_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_right (blk_mul_blk_inv γ₁ γ₂)
  have hu : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * Y q) =
        (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ * unipGL Y * AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) := by
    intro Y
    have h := hc' (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag, hDD] at h
    rw [h]
    group
  have hv : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * Y q) =
        AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * unipGL Y * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    intro Y
    have h := hc (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag] at h
    rw [h]
    group
  have hmem : ∀ (d : UPos (r + s) r → UPos (r + s) r → K) (X : UPos (r + s) r → AdeleRing (𝓞 K) K),
      X ∈ unipLattice K (r + s) r →
        (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) ∈ unipLattice K (r + s) r := by
    intro d X hX
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hX
    refine AddMonoidHom.mem_range.mpr ⟨fun p => ∑ q, d p q * y q, ?_⟩
    funext p

    simp [AddMonoidHom.compLeft_apply, map_sum, map_mul]
  have hcont : ∀ d : UPos (r + s) r → UPos (r + s) r → K,
      Continuous (fun (X : UPos (r + s) r → AdeleRing (𝓞 K) K) p =>
        ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) := by
    intro d
    refine continuous_pi fun p => ?_
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_apply q)
  have hinv1 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c' q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hv, hu]
    group
  have hinv2 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hu, hv]
    group
  let α : (UPos (r + s) r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos (r + s) r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q
      invFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * X q
      left_inv := fun X => hinv1 X
      right_inv := fun X => hinv2 X
      map_add' := by
        intro X Y
        funext p
        simp [mul_add, Finset.sum_add_distrib]
      continuous_toFun := hcont c'
      continuous_invFun := hcont c }
  have hα : ∀ X, α X ∈ unipLattice K (r + s) r ↔ X ∈ unipLattice K (r + s) r := by
    intro X
    constructor
    · intro h
      have h2 := hmem c (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) h
      rwa [hinv1] at h2
    · exact hmem c' X
  have hper : ∀ ξ ∈ unipLattice K (r + s) r, ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL (ξ + X) * g) = φ (unipGL X * g) :=
    fun ξ hξ X => hφ.unipGL_vadd g ⟨ξ, hξ⟩ X
  have hstep : ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL X * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g)) = φ (unipGL (α X) * g) := by
    intro X
    rw [← hφ (blk γ₁⁻¹ γ₂⁻¹), hDD]
    change _ = φ (unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) * g)
    rw [hu]
    group
  unfold constantTerm
  simp_rw [hstep]
  exact UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (r + s) r α hα (fun X => φ (unipGL X * g)) hper
