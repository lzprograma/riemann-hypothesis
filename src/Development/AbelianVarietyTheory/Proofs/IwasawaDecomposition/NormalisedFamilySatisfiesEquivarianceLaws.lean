module

import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetIdNormOneMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdLatGmap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOThZeroTriv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.ThetaMove.Moved

namespace GlobalTheory.Mem.NatEqui

variable {D : D7}

theorem chi_smulLat {χ : IdE D → ℂ} (hχ : IsChi D χ) {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
      χ (detId D (stdL D n) (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)) =
        (∏ τ : D.what₂.Tau, (embT D τ (γ : Matrix (Fin n) (Fin n) D.host.E).det)⁻¹) * χ (detId D (stdL D n) L) := by
  letI := D.host.cmStar
  intro γ
  have hst : ∀ x : D.host.E, star x = D.host.conj x := GlobalTheory.NormSum.AdLattice.star_eq_conj D
  let z : unitary D.host.E := ⟨_, Matrix.det_of_mem_unitary γ.2⟩
  rw [GlobalTheory.Mem.Col2.ChiFacLaw.detId_image D (stdL D n) L (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)
    (γ : Matrix (Fin n) (Fin n) D.host.E)
    (star (γ : Matrix (Fin n) (Fin n) D.host.E)) γ.2.2 (fun x hx => ⟨x, hx, rfl⟩) ?_,
    hχ.1 _ _ (GlobalTheory.Mem.Col2.ChiFacLaw.norm_one_span D z.1 (by rw [← hst]; exact z.2.2))
      (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (sd_stdL D n) hL hL).1, hχ.2 z]
  rintro _ ⟨y, hy, rfl⟩
  change (star (γ : Matrix (Fin n) (Fin n) D.host.E)).mulVec ((γ : Matrix (Fin n) (Fin n) D.host.E).mulVec y) ∈ L
  rwa [Matrix.mulVec_mulVec, γ.2.1, Matrix.one_mulVec]

theorem sd_smulLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E, SD D (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L) := by
  intro γ
  obtain ⟨g, hg⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D n L hL
  obtain ⟨γA, hγ⟩ := GlobalTheory.TrueTheta.exists_rat γ
  exact GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.TrueTheta.moves_smulLat hγ hg)

theorem chiFac_ne_zero {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L'} (h : SD D L) (h' : SD D L') :
    Base.chiFac χ N N' L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N) h))
    (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N') h'))

theorem chiFac_right {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} (L) {L' L''} (h' : SD D L') (h'' : SD D L'') :
    Base.chiFac χ N N' L L'' = χ (detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N') h' h'', mul_zpow]
  ring

theorem chiFac_left {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L₁} (L') (h : SD D L) (h₁ : SD D L₁) :
    Base.chiFac χ N N' L₁ L' = χ (detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N) h h₁, mul_zpow]
  ring

theorem eqP : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  intros
  apply Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal <;> assumption

end GlobalTheory.Mem.NatEqui
