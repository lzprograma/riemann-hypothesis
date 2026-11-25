module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
public import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsField_of :
    SplitsField := by
  intro R S K _ _ _ _ _ _ hE
  have : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  have : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance
  let q : (S →ₐ[R] K) ≃ PrimeSpectrum (K ⊗[R] S) :=
    (AlgHom.liftEquiv R K S K).trans (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (K ⊗[R] S))
  refine ⟨Finite.of_equiv _ q.symm, ?_⟩
  let e : K ⊗[R] S ≃ₐ[K] (S →ₐ[R] K) → K :=
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)).trans
      (AlgEquiv.piCongrLeft' K (fun _ => K) q.symm)
  suffices h : splitMap (fun z : S →ₐ[R] K => z) = e.toAlgHom by
    rw [Splits, h]
    exact e.bijective
  apply Algebra.TensorProduct.ext_ring
  ext s ψ
  let f : K ⊗[R] S →ₐ[K] K := AlgHom.liftEquiv R K S K ψ
  have hker : (⊥ : PrimeSpectrum K).comap f = q ψ :=
    PrimeSpectrum.ext (RingHom.ker_eq_comap_bot _).symm
  show splitMap (fun z : S →ₐ[R] K => z) (1 ⊗ₜ s) ψ =
    Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S) (1 ⊗ₜ s) (q ψ)
  rw [splitMap_tmul, one_mul, ← hker, Algebra.FormallyEtale.equivPiOfIsSepClosed_comap,
    Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply]
  simp only [f, AlgHom.liftEquiv_tmul, one_smul]
