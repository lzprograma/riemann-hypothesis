module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Flat.Stability

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_int_complex_flat (σ : Type) :
    Module.Flat (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℤ (MvPolynomial σ ℤ) ℂ (MvPolynomial σ ℂ) Algebra.IsPushout.out

theorem algebraMap_mvPolynomial_int_complex (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by
  rfl

theorem ComplexMinimalPrimesContract.proof : ComplexMinimalPrimesContract.Statement := by
  intro σ _ P hP Q hQ
  rw [← algebraMap_mvPolynomial_int_complex σ] at hQ ⊢
  have := mvPolynomial_int_complex_flat σ
  have : Q.IsPrime := hQ.isPrime
  obtain ⟨Q', hle, hprime, hover⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := P) (q := Q.under (MvPolynomial σ ℤ)) Q (Ideal.map_le_iff_le_comap.mp hQ.le)
  rw [(hQ.2 ⟨hprime, Ideal.map_le_of_le_comap hover.over.le⟩ hle).antisymm hle]
  exact hover.over.symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
