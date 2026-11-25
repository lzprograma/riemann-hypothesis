module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct

namespace GlobalTheory.CompStab

theorem idem_mul {R : Type} [CommRing R] {n : ℕ} (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (f : R)
    (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (φ : Formalism.L2.Herm.intAf F E) (hφ : φ * φ = φ)
    (x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β)
    (h : x'.1 = (φ : E ⊗[F] Formalism.L2.Herm.Af F) • x.1 + (1 - (φ : E ⊗[F] Formalism.L2.Herm.Af F)) • 1) : x' ∈ St β := by
  obtain ⟨y, rfl⟩ := hS
  refine ⟨⟨φ • y.1 + (1 - φ) • 1, φ • (y⁻¹).1 + (1 - φ) • 1, idem_mul φ hφ _ _ y.mul_inv,
    idem_mul φ hφ _ _ y.inv_mul⟩, Units.ext ?_⟩
  rw [h]
  show β.1 * (φ • y.1 + (1 - φ) • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))).map
      (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 =
    (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) + _
  rw [map_idem, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Units.mul_inv]
  rfl

theorem comm_int {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E := by
  refine AddSubgroup.closure_induction (p := fun z _ =>
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, x, rfl⟩
    have : (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E (a ⊗ₜ[F] (x : E)) : E ⊗[F] Formalism.L2.Herm.Af F) =
        ((oToS F E x : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((1 : E) ⊗ₜ[F] a) := by
      rw [oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]; rfl
    rw [this]
    exact Subring.mul_mem _ (oToS F E x).2 (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · rw [map_zero]; exact Subring.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add (f := _)]; exact Subring.add_mem _ ha hb
  · intro a _ ha
    rw [map_neg]; exact Subring.neg_mem _ ha

end General

theorem component_mem_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  intro D V β g g' f hf hg h
  let ψ : AE D →+* Lev.EAf D := (swapAE D).comp (finPart D)
  have hi : ψ f ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    comm_int (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D f) (by rw [← RingHom.map_mul, hf]))
  refine comp_mem_St β ⟨ψ f, hi⟩ (Subtype.ext ?_) (finE V g) _ hg ?_
  · show ψ f * ψ f = ψ f
    rw [← RingHom.map_mul, hf]
  · show (Formalism.L2.Theta.mt V g').map ψ = ψ f • (Formalism.L2.Theta.mt V g).map ψ + (1 - ψ f) • 1
    rw [h, map_idem]

end GlobalTheory.CompStab

end
