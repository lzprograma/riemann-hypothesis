module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqPowOfIrreducible
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.CharpolyDvd

theorem matrix_charpoly_dvd_pow {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  apply GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval <;> assumption

theorem charpoly_dvd_pow_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (G : K[X]) (hG : aeval f G = 0) :
    f.charpoly ∣ G ^ Module.finrank K V := by
  classical
  let b := Module.finBasis K V
  have hM : aeval (LinearMap.toMatrix b b f) G = 0 := by
    have := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom f G
    rw [hG, map_zero] at this
    have e : LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f := by
      ext i j
      simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [← e]
    exact this
  have := matrix_charpoly_dvd_pow _ G hM
  rwa [LinearMap.charpoly_toMatrix, Fintype.card_fin] at this

alias main := _root_.GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank

end GlobalTheory.CharpolyDvd
