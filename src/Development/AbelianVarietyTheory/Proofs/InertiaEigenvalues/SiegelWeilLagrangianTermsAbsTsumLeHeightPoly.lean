module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelHeightFinitePlaceDoublingEmbeddingLeOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelEisensteinDoubledThetaTermsEqLagrangianIntStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisPoleLEZeroOfLt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DblApply

@[expose] public section

noncomputable section

namespace GlobalTheory.SWAbsGrowth

section Local

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_le_sq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    ‖Algebra.norm (Fv F v) x‖₊ ≤ absFin F v x ^ 2 := by
  have hN := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x
  have e1 : absFin F v (algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) x)) =
      ‖Algebra.norm (Fv F v) x‖₊ := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact absFin_tmul_one F v _
  have hs : absFin F v (sigR (Fv F v) σ x) ≤ absFin F v x := by
    refine (absFin_le_iff F v).2 fun τ => ?_
    have e2 : ∀ w, finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v ((τ : E →ₐ[F] FvBar F v).comp σ) w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    rw [e2]
    exact le_absFin F v _ x
  rw [← e1, hN, sq]
  exact (absFin_mul_le F v _ _).trans (mul_le_mul' le_rfl hs)

theorem entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n ℂ) (i j : n) : ‖y i j‖₊ ≤ opNorm y := by
  have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y).le_opNNNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i = y i j := by
    change ∑ k, y i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp
  rw [h3] at h2
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h1
  exact (show ‖y i j‖₊ ≤ _ from h2).trans h1

theorem absE_le_heightGL {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ (x : GL (Fin (n + n)) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ),
      u.1 = (leviMat finSumFinEquiv x.1).det → absE F E u ≤ C * heightGL F x ^ (2 * n) := by
  refine ⟨∏ _w : InfinitePlace F, ((n.factorial : ℝ≥0) * 2 ^ n) ^ 2, fun x u hu => ?_⟩
  rw [absE_apply, heightGL, mul_pow _ _ (2 * n), ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    finprod_pow (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_absEv u) ?_ fun v => ?_)
  · obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    rw [absEw_eq_sq hσ τ, mul_comm 2 n, pow_mul, ← mul_pow]
    refine pow_le_pow_left' ?_ 2
    set H := htInf F w (bc (compInf F E w) x) with hH
    have hent : ∀ i j, ‖infEmb τ (compInf F E w (x.1 i j))‖₊ ≤ H := fun i j =>
      (entry_le_opNorm ((x.1.map (compInf F E w)).map (infEmb τ)) i j).trans
        (((normInf_le_iff F w).1 le_rfl τ).trans (le_htOf (normInf F w) (bc (compInf F E w) x)))
    have e : infEmb τ (unitInf F E w u).1 =
        (leviMat finSumFinEquiv ((x.1.map (compInf F E w)).map (infEmb τ))).det := by
      rw [leviMat_map, leviMat_map, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        ← RingHom.map_det, ← hu]
      rfl
    rw [e, Matrix.det_apply]
    refine (nnnorm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ ((2 * H) ^ n) fun s _ => ?_).trans (le_of_eq ?_))
    · have : ‖Equiv.Perm.sign s • ∏ i, leviMat finSumFinEquiv ((x.1.map (compInf F E w)).map (infEmb τ)) (s i) i‖₊ =
          ∏ i, ‖leviMat finSumFinEquiv ((x.1.map (compInf F E w)).map (infEmb τ)) (s i) i‖₊ := by
        rw [← nnnorm_prod]
        rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp [h]
      rw [this]
      refine (Finset.prod_le_pow_card _ _ (2 * H) fun i _ => ?_).trans (by simp)
      rw [two_mul]
      exact (nnnorm_add_le _ _).trans (add_le_add (hent _ _) (hent _ _))
    · simp [Fintype.card_perm, mul_pow, mul_assoc]
  · exact (finite_mulSupport_htFin F x).subset fun v hv h => hv (by simp only [h, one_pow])
  · have e : (unitFin F E v u).1 = (leviMat finSumFinEquiv (x.1.map (compFin F E v))).det := by
      rw [leviMat_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hu]
      rfl
    rw [absEv_apply, e, mul_comm 2 n, pow_mul]
    refine (absNorm_le_sq hσ v _).trans (pow_le_pow_left' ((GlobalTheory.Core.Rk.HgtFin.absFin_det_le v _).trans
      (pow_le_pow_left' ((normFin_le_iff F v).2 fun i j => ?_) n)) 2)
    have hent : ∀ i j, absFin F v ((x.1.map (compFin F E v)) i j) ≤ htFin F v (bc (compFin F E v) x) := fun i j =>
      (absFin_le_normFin F v _ i j).trans (le_htOf (normFin F v) (bc (compFin F E v) x))
    exact (absFin_add_le F v _ _).trans (max_le (hent _ _) (hent _ _))

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.Doubling
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero delta)
open scoped NNReal

variable {D : D7}

theorem hgt_mul_le (A : HSp D) (a : GL (Fin A.rank) (AE D)) (ha : IsMaj A a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : GA D (dblSp A),
      (hgt A a (x * y) : ℝ) ≤ hgt A a x * (C * GlobalTheory.Grow.height (dblSp A) y ^ (2 * A.rank)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hK := isCompact_Khat A a
  obtain ⟨C, hC⟩ := absE_le_heightGL (isCMExt_host D) A.rank
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact (dblSp A) hK
  have hB0 : 0 ≤ B := (GlobalTheory.Grow.height_pos _ _).le.trans (hB 1 (one_mem _))
  refine ⟨C * (B * B) ^ (2 * A.rank), by positivity, fun x y => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := hI x
  obtain ⟨p', k', hk', e⟩ := hI (k * y)
  have h1 : hgt A a (p * k * y) = absA D (aP A p) * absA D (aP A p') := by
    rw [mul_assoc, e, ← mul_assoc, ← Subgroup.coe_mul, hgt_mul A a _ hk', map_mul, map_mul]
  rw [h1, hgt_mul A a _ hk, NNReal.coe_mul]
  refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
  have h2 : (absA D (aP A p') : ℝ) ≤ C * GlobalTheory.Grow.height (dblSp A) p' ^ (2 * A.rank) := by
    have := hC (Formalism.L2.Theta.matHom (dblSp A) p') (aP A p') rfl
    unfold GlobalTheory.Grow.height
    exact_mod_cast this
  have h3 : GlobalTheory.Grow.height (dblSp A) p' ≤ B * B * GlobalTheory.Grow.height (dblSp A) y := by
    have e' : (p' : GA D (dblSp A)) = k * y * k'⁻¹ := by rw [e, mul_inv_cancel_right]
    have hy := (GlobalTheory.Grow.height_pos _ y).le
    calc _ = GlobalTheory.Grow.height (dblSp A) (k * y * k'⁻¹) := by rw [e']
      _ ≤ GlobalTheory.Grow.height (dblSp A) k * GlobalTheory.Grow.height (dblSp A) y * GlobalTheory.Grow.height (dblSp A) k'⁻¹ :=
        (GlobalTheory.Grow.height_mul_le _ _ _).trans
          (mul_le_mul_of_nonneg_right (GlobalTheory.Grow.height_mul_le _ _ _) (GlobalTheory.Grow.height_pos _ _).le)
      _ ≤ B * GlobalTheory.Grow.height (dblSp A) y * B :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hB k hk) hy) (hB _ (inv_mem hk')) (GlobalTheory.Grow.height_pos _ _).le
          (by positivity)
      _ = _ := by ring
  rw [mul_assoc, ← mul_pow]
  exact h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le h3 _) C.coe_nonneg)

theorem norm_swSec_le {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ : (AE D)ˣ →* Circle}
    {omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} (hω : IsWeilDatumO ψ (dblSp A) B 1 χ omh)
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓕) {φ : WO (dblSp A) B → ℂ}
    (hφ : IsThetaFunO ψ (dblSp A) B φ) (a : GL (Fin A.rank) (AE D)) (ha : IsMaj A a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖swSec A B omh ν 𝓕 φ x‖ ≤ C * (hgt A a x : ℝ) ^ ((B.rank : ℝ) / 2) := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hc := (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ omh hω ν 𝓕 hν φ hφ).2
  obtain ⟨C, hC⟩ := (isCompact_Khat A a).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, (norm_nonneg _).trans (hC 1 (one_mem _)), fun x => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := hI x
  have ex : (sZero A B + (A.rank : ℂ) / 2).re = (B.rank : ℝ) / 2 := by
    simp only [sZero, Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]; ring
  rw [GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ omh hω ν 𝓕 hν φ hφ p k, norm_mul, norm_mul, Circle.norm_coe,
    one_mul, norm_npow (hom_pos _ _), ex, hgt_mul A a p hk, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (by positivity)

end Global

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift

end Main

end GlobalTheory.SWAbsGrowth

end
