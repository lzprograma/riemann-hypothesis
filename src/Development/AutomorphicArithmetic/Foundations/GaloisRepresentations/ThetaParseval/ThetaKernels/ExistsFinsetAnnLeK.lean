module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroup
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsCompactOfFinite
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralCompAddEquiv
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SetIntegralAddRight
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SmulMemConjHalf
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaFunOrientedModelCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAMulEqZeroIffSnd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace

/-! # ExistsFinsetAnnLeK: Consolidated global theta-kernel definitions and proofs (ExistsFinsetAnnLeK). -/
@[expose] public section

open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open UpperTheory.TP.W (GoodK)

noncomputable section
open AddChar (map_add_eq_mul map_zero_eq_one)
namespace GlobalTheory.SplitLagrF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF GlobalTheory.SplitInvFormF
theorem exists_finset_ann_le_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  classical
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AEF F E) := eh.isEmbedding.t2Space
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := id he
  obtain ⟨N, Φ, hΦc, hΦi, hΦr⟩ := GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT
  have hV : (Φ ⁻¹' (U : Set (WOF F E nS nT))) ∈ nhds (0 : Fin N → v.adicCompletion F) :=
    (hU.preimage hΦc).mem_nhds (by rw [Set.mem_preimage, map_zero]; exact U.zero_mem)
  obtain ⟨K, hK, hK0, hKn⟩ := GlobalTheory.NonarchShell.exists_compact_shell_nsmul F v N _ hV
  let Y : Set (WOF F E nS nT) := {y | ∀ i j, cAF σ e * y i j = y i j}
  have hYc : IsClosed Y := by
    simp only [Y, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hYε : ∀ y ∈ Y, ∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j := by
    intro y hy i j
    rw [← hsum, ← hy i j]
    linear_combination (y i j) * he2 + (y i j) * hcc
  have hYn : ∀ y ∈ Y, ∀ n : ℕ, n • y ∈ Y := by
    intro y hy n i j
    show cAF σ e * (n • y i j) = n • y i j
    rw [mul_smul_comm, hy i j]
  let χ : WOF F E nS nT → WOF F E nS nT → ℂ := fun g y =>
    B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g)
  have hχc : ∀ g, Continuous (χ g) := fun g =>
    hψ.comp ((GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left
      g))
  have hχn : ∀ g y (n : ℕ), χ g (n • y) = χ g y ^ n := by
    intro g y n
    induction n with
    | zero =>
      simp only [χ, zero_smul, GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right,
        sub_zero,
        map_zero_eq_one, pow_zero]
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      simp only [χ]
      rw [GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right,
        ← map_add_eq_mul]
      congr 1
      ring
  let S := Φ '' K ∩ Y
  have hSc := (hK.image hΦc).inter_right hYc
  have hSdet : ∀ s ∈ S, ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧ χ g s ≠ 1 := by
    rintro s ⟨⟨k, hk, rfl⟩, hsY⟩
    refine exists_detect (GlobalTheory.SplitDetCharF.sig_invol hB.cm) hB.std hS hT hξ hσξ he _ hsY ?_
    intro h0
    apply hK0
    rw [← map_zero Φ] at h0
    rwa [hΦi h0] at hk
  choose! gs hgsX hgsχ using hSdet
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun s : S => {y | χ (gs s.1) y ≠ 1})
    (fun s => isOpen_ne_fun (hχc _) continuous_const) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hgsχ s hs⟩)
  refine ⟨t.image (fun s : S => gs s.1), ?_, ?_⟩
  · intro g hg
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgsX s.1 s.2
  · intro y hy hG
    by_contra hyU
    obtain ⟨t0, rfl⟩ := hΦr _ (hYε _ hy)
    obtain ⟨n, hn⟩ := hKn t0 hyU
    have hmem : Φ (n • t0) ∈ S := ⟨⟨_, hn, rfl⟩, by rw [map_nsmul]; exact hYn _ hy n⟩
    obtain ⟨s, hs, hsy⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hsy
    show χ (gs s.1) (Φ (n • t0)) = 1
    rw [map_nsmul, hχn]
    have := hG (gs s.1) (Finset.mem_image_of_mem (fun s : S => gs s.1) hs)
    simp only [χ] at this ⊢
    rw [this, one_pow]
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
variable {B : Base F E}
theorem exists_open_sep_k (hB : GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠
  0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (U : AddSubgroup (conjHalf σ e nS nT))
    (hU : IsOpen (U : Set (conjHalf σ e nS nT))) :
    ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, g ∈ conjHalf σ (cAF σ e) nS nT) ∧
      ∀ y : conjHalf σ e nS nT, (∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ U := by
  obtain ⟨G, hG1, hG2⟩ := exists_finset_ann_le_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e
    he
    (U.comap (projH σ nS nT he.1)) (hU.preimage (continuous_projH he.1))
  refine ⟨G, fun g hg => GlobalTheory.SplitVacF.mem_conjHalf_conj he (hG1 g hg), fun y hy => ?_⟩
  have := hG2 y.1 y.2 hy
  rwa [AddSubgroup.mem_comap, projH_coe] at this
theorem exists_compact_ann_k (hB : GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀
  ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (P : WOF F E nS nT → Prop)
    (hP : ∀ g ∈ conjHalf σ (cAF σ e) nS nT, ∃ k : ℕ, 0 < k ∧ P (k • g)) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ y : conjHalf σ e nS nT, (∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ K := by
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  obtain ⟨K₀, hKo, hKc⟩ := exists_compact_open he
  obtain ⟨G, hG1, hG2⟩ := exists_open_sep_k hB hS hT hξ hσξ he K₀ hKo
  choose! k hk0 hk using hP
  refine (exists_compact_of_finite hKc
    (fun (y : conjHalf σ e nS nT) (g : G) => commF σ JS JT ξ₀ B.ψ g y)
    {y | ∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1} ?_ ?_).imp fun K h => ⟨h.1, fun y hy => h.2 hy⟩
  · refine (Set.Finite.pi' (t := fun g : G => ((Polynomial.nthRoots (k g) (1 : ℂ)).toFinset : Set ℂ))
      fun g => Finset.finite_toSet _).subset ?_
    rintro _ ⟨y, hy, rfl⟩ g
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (hk0 _ (hG1 _ g.2)),
      ← GlobalTheory.SplitVacF.commF_nsmul_left]
    exact hy _ (hk _ (hG1 _ g.2))
  · intro y y' h
    refine hG2 _ fun g hg => ?_
    have h1 := congrFun h ⟨g, hg⟩
    rw [sub_eq_neg_add, AddSubgroup.coe_add, AddSubgroup.coe_neg, GlobalTheory.SplitVacF.commF_add_right, h1,
      GlobalTheory.SplitVacF.commF_neg_right]
end GlobalTheory.SplitLagrF
end

noncomputable section
namespace GlobalTheory.HeisThetaF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isThetaFunOF_heisOF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT ξ₀ w₀ f hf
  have hψ : Continuous B.ψ := hB.std.1
  have := isTopologicalRing_AEF (F := F) (E := E)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    simp only [heisOF]
    rw [add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K, hK⟩ := exists_openAddSubgroup_psi_fin B.ψ hψ
    let φ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u
        map_zero' := by simp only [symplOHF_zero_left, symplOHF_zero_right, sub_zero]
        map_add' := fun u v => by simp only [symplOHF_add_left, symplOHF_add_right]; abel }
    have hφ : Continuous φ := (continuous_symplOHF_left w₀).sub (continuous_symplOHF_right w₀)
    let ρ : WOF F E nS nT →+ Af F := (sndA F).toRingHom.toAddMonoidHom.comp φ
    have hρ : Continuous ρ := continuous_snd.comp hφ
    refine ⟨U ⊓ K.toAddSubgroup.comap ρ, hU.inter (K.isOpen.preimage hρ), fun u hu h0 => ?_⟩
    have h1 : pairA F 1 0 • u = 0 := smul_eq_zero_of_map_infPartF h0
    have hfst : fstA F (φ u) = 0 := by
      rw [← fstA_mul_idem]
      show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)) = 0
      rw [mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, h1, symplOHF_zero_left, symplOHF_zero_right,
        sub_zero, map_zero]
    have hφu : φ u = pairA F 0 (ρ u) := Prod.ext hfst rfl
    have hone : B.ψ (φ u) = 1 := by rw [hφu]; exact hK _ hu.2
    have hswap : B.ψ (symplOHF σ JS JT ξ₀ u w₀) = B.ψ (symplOHF σ JS JT ξ₀ w₀ u) := by
      have : symplOHF σ JS JT ξ₀ u w₀ = φ u + symplOHF σ JS JT ξ₀ w₀ u := by
        show _ = (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) + _
        abel
      rw [this, AddChar.map_add_eq_mul, hone, one_mul]
    funext w
    have hw := congrFun (hUf u hu.1 h0) (w + w₀)
    simp only [heisOF] at hw ⊢
    rw [← hw, add_right_comm w u w₀, symplOHF_add_left w u w₀, symplOHF_add_left w w₀ u, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, hswap]
    ring
  · show Continuous fun w => B.ψ (symplOHF σ JS JT ξ₀ w w₀) * f (w + w₀)
    exact (hψ.comp (continuous_symplOHF_left w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · intro k L hL h0 w
    let φ₁ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀
        map_zero' := symplOHF_zero_left w₀
        map_add' := fun u v => symplOHF_add_left u v w₀ }
    let ev : AF F →+ ℝ :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.toAddMonoidHom.comp (fstA F).toRingHom.toAddMonoidHom)
    have hev : Continuous ev :=
      (LinearMap.continuous_of_finiteDimensional (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).comp
        ((continuous_ringEquiv_mixedSpace F).comp continuous_fst)
    let g : (Fin k → ℝ) →+ ℝ := ev.comp (φ₁.comp L)
    have hg : Continuous g := hev.comp ((continuous_symplOHF_left w₀).comp hL)
    let gL := g.toRealLinearMap hg
    have hval : ∀ t, B.ψ (symplOHF σ JS JT ξ₀ (L t) w₀) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) := by
      intro t
      have hfin : sndA F (symplOHF σ JS JT ξ₀ (L t) w₀) = 0 := by
        have h1 : pairA F 0 1 • L t = 0 := smul_eq_zero_of_map_finPartF (h0 t)
        rw [← sndA_mul_idem, ← symplOHF_smul_left, h1, symplOHF_zero_left, map_zero]
      rw [hB.std.2.2 _ ?_]
      · rfl
      · intro v hv
        have hv1 : v.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hv
        refine Prod.ext ?_ ?_
        · show v.1 * (symplOHF σ JS JT ξ₀ (L t) w₀).1 = 0
          rw [hv1, zero_mul]
        · show v.2 * (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0
          rw [show (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0 from hfin, mul_zero]
    have hfun : (fun t => heisOF σ JS JT ξ₀ B.ψ w₀ f (w + L t)) = fun t =>
        B.ψ (symplOHF σ JS JT ξ₀ w w₀) * Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) *
          f (w + w₀ + L t) := by
      funext t
      simp only [heisOF]
      rw [symplOHF_add_left, AddChar.map_add_eq_mul, hval, add_right_comm]
    rw [hfun]
    refine (contDiff_const.mul ?_).mul (hf.smooth k L hL h0 (w + w₀))
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp gL.contDiff)).cexp
end GlobalTheory.HeisThetaF
end

section
open scoped ContDiff TensorProduct Matrix
open Formalism.IndefR.DatumF GlobalTheory.SWQ GlobalTheory.ThetaTransform NumberField IsDedekindDomain
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThetaTransformF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem isThetaFunOF_thV_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ hstd N e he hrat Φ hΦ
  have hR := hB.cm.1
  have hψ := hstd.1
  obtain ⟨hc, -, hfin, hinf⟩ := coordF nT nS N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Continuous (thV B.ψ Φ) := fun Φ hΦ =>
    _root_.GlobalTheory.ThetaTransform.continuous_thV F N B.ψ hR hψ Φ
      (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ hΦ)
  refine ⟨fun γ w => ?_, ?_, (hcont Φ hΦ).comp hc, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    simp only [Function.comp_apply, map_add (f := _), symplOHF_eq he, h]
    exact quasiV_thV B.ψ hψ.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := _root_.GlobalTheory.WeilLevel.schA_level F N B.ψ hR hψ Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisOF_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · intro k L hL hL0 w
    have h := contDiff_of_heisV_closed B.ψ hψ.1 {g | ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), g = thV B.ψ Φ}
      (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hcont Φ hΦ)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ M hM
        obtain ⟨Φ', hΦ', hd⟩ := _root_.GlobalTheory.ThetaTransform.hasDerivAt_heisV_line F N B.ψ hR hψ Φ hΦ
          M hM
        exact ⟨_, ⟨Φ', hΦ', rfl⟩, hd⟩)
      _ ⟨Φ, hΦ, rfl⟩ k (e.toLinearMap.toAddMonoidHom.comp L) (hc.comp hL) (fun t => (hfin _).1 (hL0 t)) (e w)
    simpa [Function.comp_def] using h
end GlobalTheory.ThetaTransformF
end
end

section
open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
open GlobalTheory.LagrTheta (lagrInt)
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open UpperTheory.TP.W (GoodK)
noncomputable section
namespace GlobalTheory.SplitLagrF
theorem lagrInt_heis_dC_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f → ∀ v : WOF F E nS nT,
        lagrInt ν 𝓕 (dC F E nT)
                     (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * v) f) =
          lagrInt ν 𝓕 (dC F E nT) f := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ ν 𝓕 _ h𝓕 f hf u
  set g : WOF F E nS nT → ℂ := fun v => f (dC F E nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * u) f
      (dC F E nT * v) = g (v + u) := by
    intro v
    simp only [hg, heisOF]
    rw [symplOHF_dC, AddChar.map_zero_eq_one, one_mul, Matrix.mul_add]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    show f (dC F E nT * ((ratWF γ : WOF F E nS nT) + v)) = f (dC F E nT * v)
    have hq := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (dC F E nT * v)
    rw [← dC_mul_ratWF, symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
    rw [Matrix.mul_add, hq]
  unfold lagrInt
  simp_rw [h1]
  exact setIntegral_add_right ν 𝓕 h𝓕 g h2 u
end GlobalTheory.SplitLagrF
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
open GlobalTheory.LagrTheta (lagrInt)
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open UpperTheory.TP.W (GoodK)
noncomputable section
namespace GlobalTheory.SplitLagrF
open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ :
  AddChar (AF F) ℂ}
variable {B : Base F E}
theorem prof_add_k (hB : GoodK σ B) {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν
  : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f g : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (hg : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g) (y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (f + g) y = prof σ JS JT ξ₀ B.ψ ν 𝓕 f y + prof σ JS JT ξ₀ B.ψ ν 𝓕 g y := by
  unfold prof
  rw [GlobalTheory.WeilPartsF.heisOF_add]
  exact integral_add
    (integrableOn_dC hν h𝓕 (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y)
      f hf))
    (integrableOn_dC hν h𝓕 (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y)
      g hg))
theorem prof_heis_dC_k (hB : GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0)
  (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (a y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * a) f) y =
      commF σ JS JT ξ₀ B.ψ y (a + a) * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  unfold prof
  rw [heisOF_comm, lagrInt_smul, commF_aC_dC, lagrInt_heis_dC_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 _
    (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf)]
theorem prof_heis_lift_k (hB : GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠
  0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (g y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f) y =
      commF σ JS JT ξ₀ B.ψ g y * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  rw [prof_heis_dC_k hB hS hT hξ hσξ hν h𝓕 hf, neg_hlf_add, GlobalTheory.SplitVacF.commF_swap]
end GlobalTheory.SplitLagrF
end
end

section
abbrev _root_.GlobalTheory.T.schrodinger_model_isomorphism :=
  GlobalTheory.ThetaTransformF.isThetaFunOF_thV_k
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
open UpperTheory.TP.W (GoodK)
noncomputable section
namespace GlobalTheory.SplitLagrF
open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
variable {B : Base F E}
theorem prof_support_k (hB : GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0)
  (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ t : conjHalf σ e nS nT, t ∉ K → prof σ JS JT ξ₀ B.ψ ν 𝓕 f t = 0 := by
  obtain ⟨K, hK, hKs⟩ := exists_compact_ann_k hB hS hT hξ hσξ he
    (fun g => heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f = f) (fun g hg => by
      obtain ⟨k, hk, h⟩ := exists_nsmul_fix (GlobalTheory.SplitVacF.isSplitIdemF_conj he)
        (mul_mem_conjHalf (dC F E nT) (smul_mem_conjHalf (-hlf F E) hg)) hf
      refine ⟨k, hk, ?_⟩
      rwa [smul_comm, Matrix.mul_smul])
  refine ⟨K, hK, fun t ht => ?_⟩
  by_contra hne
  refine ht (hKs t fun g hg => ?_)
  have h := prof_heis_lift_k hB hS hT hξ hσξ hν h𝓕 hf g t
  rw [hg] at h
  exact (mul_eq_right₀ hne).1 h.symm
theorem prof_integrable_k (hB : GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠
  0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    Integrable (fun t : conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) μ := by
  obtain ⟨-, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : T2Space (conjHalf σ e nS nT) := inferInstance
  have : R1Space (conjHalf σ e nS nT) := T2Space.r1Space
  obtain ⟨U, hU, hUf⟩ := prof_level (JT := JT) ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := prof_support_k hB hS hT hξ hσξ hν h𝓕 he hf
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK hKs)
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hn : {s : conjHalf σ e nS nT | s - t ∈ U} ∈ nhds t := by
    refine IsOpen.mem_nhds (hU.preimage (continuous_id.sub continuous_const)) ?_
    show t - t ∈ U
    rw [sub_self]; exact U.zero_mem
  filter_upwards [hn] with s hs
  have h1 := hUf t _ hs
  rwa [add_sub_cancel] at h1
theorem commF_eventually_k (hB : GoodK σ B) {e : AEF F E} (he : IsSplitIdemF σ e) (g : WOF F E
  nS nT) :
    ∀ᶠ y : conjHalf σ e nS nT in nhds 0, commF σ JS JT ξ₀ B.ψ g y = 1 := by
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨K, hK⟩ := GlobalTheory.HeisThetaF.exists_openAddSubgroup_psi_fin B.ψ hψ
  let φ : WOF F E nS nT → AF F := fun u => symplOHF σ JS JT ξ₀ g u - symplOHF σ JS JT ξ₀ u g
  have hφ : Continuous φ :=
    (GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g)
  let ρ : conjHalf σ e nS nT → Af F := fun u => (φ u.1).2
  have hρ : Continuous ρ := continuous_snd.comp (hφ.comp continuous_subtypeVal)
  have h0 : ρ 0 = 0 := by
    show (symplOHF σ JS JT ξ₀ g 0 - symplOHF σ JS JT ξ₀ 0 g).2 = 0
    rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero]
    rfl
  have hn : ρ ⁻¹' (K : Set (Af F)) ∈ nhds (0 : conjHalf σ e nS nT) :=
    (K.isOpen.preimage hρ).mem_nhds (by rw [Set.mem_preimage, h0]; exact K.zero_mem)
  filter_upwards [hn] with u hu
  have h1 : pairA F 1 0 • u.1 = 0 :=
    GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (GlobalTheory.SplitVacF.fin_of_mem he u.2)
  have hfst : fstA F (φ u.1) = 0 := by
    rw [← GlobalTheory.HeisThetaF.fstA_mul_idem]
    show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ g u.1 - symplOHF σ JS JT ξ₀ u.1 g)) = 0
    rw [mul_sub, ← GlobalTheory.HeisThetaF.symplOHF_smul_left (pairA F 1 0) u.1 g,
      ← GlobalTheory.HeisThetaF.symplOHF_smul_right (pairA F 1 0) g u.1, h1, GlobalTheory.HeisThetaF.symplOHF_zero_left,
      GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, map_zero]
  have hφu : φ u.1 = pairA F 0 (ρ u) := Prod.ext hfst rfl
  show B.ψ (φ u.1) = 1
  rw [hφu]
  exact hK _ hu
theorem lagrInt_eq_zero_k (hB : GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠
  0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f)
    (hall : ∀ u, ∫ t : conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ u f) t ∂μ = 0) :
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f = 0 := by
  obtain ⟨U, hU, hUf⟩ := prof_level ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := prof_support_k hB hS hT hξ hσξ hν h𝓕 he hf
  obtain ⟨G, -, hG⟩ := exists_open_sep_k hB hS hT hξ hσξ he U hU
  let L : AddSubgroup (conjHalf σ e nS nT) :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, GlobalTheory.SplitVacF.commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => GlobalTheory.SplitVacF.commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := GlobalTheory.SplitVacF.commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g
          (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hL : IsOpen (L : Set (conjHalf σ e nS nT)) := by
    refine AddSubgroup.isOpen_of_mem_nhds L (g := 0) ?_
    exact (Filter.eventually_all_finset G).2 fun g _ => commF_eventually_k hB he g
  have hφ := GlobalTheory.fourier_uniqueness_of_openSubgroup μ
    (fun (a : WOF F E nS nT) (t : conjHalf σ e nS nT) => commF σ JS JT ξ₀ B.ψ a t)
    (fun a s t => GlobalTheory.SplitVacF.commF_add_right a s.1 t.1)
    (fun a => GlobalTheory.SplitVacF.commF_zero_right a) (fun t => GlobalTheory.SplitVacF.commF_zero_left t.1)
    (fun a b t => GlobalTheory.SplitVacF.commF_add_left a b t.1) L hL
    (fun x hx => by
      have hx' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (x : WOF F E nS nT) = 1 := hx
      push Not at hx'
      obtain ⟨g, hg, hne⟩ := hx'
      exact ⟨g, fun l hl => hl g hg, hne⟩)
    (fun t => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) K hK hKs (fun t l hl => hUf t l (hG l hl))
    (fun a _ => by
      rw [← hall (dC F E nT * ((-hlf F E) • a : WOF F E nS nT))]
      simp only [prof_heis_lift_k hB hS hT hξ hσξ hν h𝓕 hf])
  rw [← prof_zero (ψ := B.ψ)]
  exact congrFun hφ 0
end GlobalTheory.SplitLagrF
end
end

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF MeasureTheory
  GlobalTheory.SplitInvFormF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
  GlobalTheory.TransportF GlobalTheory.WeilSchrodinger GlobalTheory.DblSplitForm
  PositivityTheory.ThKW.SplitVacuumEigenvectors
theorem GlobalTheory.T.exists_split_functional_doubled :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ e, IsSplitIdemF σ e →
        ∃ ℓ : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS (nT + nT), (∀ i j, cAF σ e * u i j = u i j) →
            ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
              ℓ (heisOF σ JS (dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (deltaT f₁ f₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ e he
  classical
  have hf₀_ex : ∃ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
    have hstd := GlobalTheory.T.standard_additive_character_sign F E σ B hB
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hσ : ∀ x, σ (σ x) = x := fun x => by
      apply ((B.emb w).1 : E →+* ℂ).injective
      rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
    have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
    have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
    let JA : Matrix (Fin nT) (Fin nT) E := JTᵀ
    let JB : Matrix (Fin nS) (Fin nS) E := -(ξ₀ • JS⁻¹)
    have hSinv := GlobalTheory.ThetaNonzeroF.herm_inv_entry σ JS hS.1 (Ne.isUnit hS.2)
    have hA : ∀ i j, σ (JA j i) = JA i j := fun i j => hT.1 j i
    have hBs : ∀ i j, σ (JB j i) = -JB i j := fun i j => by
      simp only [JB, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσξ, hSinv]; ring
    have hA' : JA.det ≠ 0 := by simp only [JA, Matrix.det_transpose]; exact hT.2
    have hB' : JB.det ≠ 0 := by
      simp only [JB, Matrix.det_neg, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : E) ≠ 0))
        (mul_ne_zero (pow_ne_zero _ hξ0) (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).ne_zero)
    obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hA hBs hA' hB'
    let co' : Darboux (symp (cA σ) (-1 : AF F ⊗[F] E) (incM F JA) (incM F JB)) (Fin nT × Fin nS) := co
    have hJB : (-1 : AF F ⊗[F] E) • incM F JB = incM F (ξ₀ • JS⁻¹) := by ext i j; simp [JB, incM]
    let τ := Fintype.equivFin (Fin nT × Fin nS)
    have he' : ∀ w w', symplOF σ JS JT ξ₀ w w' =
        GlobalTheory.ThetaTransform.symV (numCoordF co' τ w) (numCoordF co' τ w') := fun w w' => by
      rw [symplOF_eq_symp rfl hJB, co'.form]
      simp only [GlobalTheory.ThetaTransform.symV, numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
    have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
        numCoordF co' τ (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
      obtain ⟨y, z, h⟩ := hco x
      exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [numCoordF_apply]; erw [h]; rfl⟩
    obtain ⟨Φ, hΦ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin nT × Fin nS)
    refine ⟨thetaTr F co' B.ψ Φ, ?_, ?_⟩
    · rw [thetaTr_eqF co' τ]
      exact GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hstd _
        (numCoordF co' τ) he' hr _ (comp_mem_schA τ hΦ)
    · intro h
      have h0 := congrFun h 0
      apply hne
      have hs : schr B.ψ (0 : (Fin nT × Fin nS → AF F) × (Fin nT × Fin nS → AF F)) Φ = Φ := by
        funext x; simp [schr]
      simpa [thetaTr, Darboux.rho, hs] using h0
  obtain ⟨f₀, hf₀, hf₀0⟩ := hf₀_ex
  have he' := _root_.GlobalTheory.SplitVacF.isSplitIdemF_conj he
  let Y := conjHalf σ e nS nT
  let X := conjHalf σ (cAF σ e) nS nT
  obtain ⟨U, hU, hUf⟩ := hf₀.level
  obtain ⟨G, hGX, hGU⟩ := GlobalTheory.SplitLagrF.exists_finset_ann_le_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
    e he U hU
  have hGX' : ∀ g ∈ G, g ∈ X := fun g hg => _root_.GlobalTheory.SplitVacF.mem_conjHalf_conj he (hGX g hg)
  let YK : AddSubgroup (WOF F E nS nT) :=
    { carrier := {y | y ∈ Y ∧ ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1}
      add_mem' := fun ha hb => ⟨Y.add_mem ha.1 hb.1, fun k hk hkf => by
        rw [_root_.GlobalTheory.SplitVacF.commF_add_right, ha.2 k hk hkf, hb.2 k hk hkf, one_mul]⟩
      zero_mem' := ⟨Y.zero_mem, fun k _ _ => _root_.GlobalTheory.SplitVacF.commF_zero_right k⟩
      neg_mem' := fun {a} ha => ⟨Y.neg_mem ha.1, fun k hk hkf => by
        have := _root_.GlobalTheory.SplitVacF.commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) k a
        rwa [ha.2 k hk hkf, mul_one] at this⟩ }
  let Q : AddSubgroup YK :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun ha hb g hg => by rw [AddSubgroup.coe_add, _root_.GlobalTheory.SplitVacF.commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => _root_.GlobalTheory.SplitVacF.commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := _root_.GlobalTheory.SplitVacF.commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hQfix : ∀ q ∈ Q, heisOF σ JS JT ξ₀ B.ψ (q : WOF F E nS nT) f₀ = f₀ :=
    fun q hq => hUf _ (hGU _ q.2.1 hq) (_root_.GlobalTheory.SplitVacF.fin_of_mem he q.2.1)
  choose! Ng hNg0 hNg using fun g (hg : g ∈ G) => exists_nsmul_fix he' (hGX' g hg) hf₀
  set N := ∏ g ∈ G, Ng g
  have hN0 : 0 < N := Finset.prod_pos fun g hg => hNg0 g hg
  have hpowN : ∀ g ∈ G, ∀ y : YK, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) ^ N = 1 := fun g hg y => by
    obtain ⟨m, hm⟩ : Ng g ∣ N := Finset.dvd_prod_of_mem _ hg
    rw [← _root_.GlobalTheory.SplitVacF.commF_nsmul_left]
    refine y.2.2 _ (nsmul_mem (hGX' g hg) N) ?_
    rw [hm, mul_nsmul]
    exact heisOF_nsmul_fix he' (nsmul_mem (hGX' g hg) _) (hNg g hg) m
  have : Finite (YK ⧸ Q) := by
    let S := (Polynomial.nthRoots N (1 : ℂ)).toFinset
    refine Finite.of_injective (β := G → S) (fun a g => ⟨commF σ JS JT ξ₀ B.ψ g (Quotient.out a : YK),
      Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots hN0).2 (hpowN g g.2 _))⟩) (fun a b hab => ?_)
    rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq]
    intro g hg
    have h1 := congrArg Subtype.val (congrFun hab ⟨g, hg⟩)
    simp only at h1
    show commF σ JS JT ξ₀ B.ψ g ((-Quotient.out a + Quotient.out b : YK) : WOF F E nS nT) = 1
    rw [AddSubgroup.coe_add, _root_.GlobalTheory.SplitVacF.commF_add_right, ← h1, AddSubgroup.coe_neg, _root_.GlobalTheory.SplitVacF.commF_neg_right]
  let Ch : Set (YK → ℂ) :=
    {χ | ∃ x ∈ X, (∀ q ∈ Q, commF σ JS JT ξ₀ B.ψ x (q : WOF F E nS nT) = 1) ∧
      χ = fun y : YK => commF σ JS JT ξ₀ B.ψ x (y : WOF F E nS nT)}
  obtain ⟨χ, ⟨x, hxX, -, rfl⟩, w, hwspan, hw0, hweig⟩ := exists_eigen_of_sep
    (fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT)) (fun a b f => _root_.GlobalTheory.SplitVacF.heisOF_add_half he a.2.1 b.2.1 f)
    Q f₀ hf₀0 hQfix Ch
    (by rintro _ ⟨x, -, -, rfl⟩ a b; exact _root_.GlobalTheory.SplitVacF.commF_add_right x a b)
    (by rintro _ ⟨x, -, hx, rfl⟩ q hq; exact hx q hq)
    (by
      rintro _ ⟨x, hx, hxQ, rfl⟩ _ ⟨x', hx', hxQ', rfl⟩
      refine ⟨x + x', X.add_mem hx hx', fun q hq => by rw [_root_.GlobalTheory.SplitVacF.commF_add_left, hxQ q hq, hxQ' q hq, one_mul], ?_⟩
      funext y; simp only [Pi.mul_apply, _root_.GlobalTheory.SplitVacF.commF_add_left])
    ⟨0, X.zero_mem, fun q _ => _root_.GlobalTheory.SplitVacF.commF_zero_left _, by funext y; simp only [Pi.one_apply, _root_.GlobalTheory.SplitVacF.commF_zero_left]⟩
    (fun y hy => by
      have hy' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1 := hy
      push Not at hy'
      obtain ⟨g, hg, hne⟩ := hy'
      exact ⟨_, ⟨g, hGX' g hg, fun q hq => hq g hg, rfl⟩, hne⟩)
  have hspan_theta : Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩; exact GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hf₀)
  have hspan_fix : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ →
      Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      LinearMap.eqLocus (heisL σ JS JT ξ₀ B.ψ k) LinearMap.id := fun k hk hkf => Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    show heisOF σ JS JT ξ₀ B.ψ k (heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) =
      heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀
    rw [heisOF_comm, y.2.2 k hk hkf, one_smul, hkf])
  have hφ : IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ (-x) w) :=
    GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ (hspan_theta hwspan)
  have hφ0 : heisOF σ JS JT ξ₀ B.ψ (-x) w ≠ 0 := fun h0 => hw0 <| by
    have := _root_.GlobalTheory.SplitVacF.heisOF_add_half (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) he' hxX (X.neg_mem hxX) w
    rw [add_neg_cancel, heisOF_zero] at this
    rw [this, show heisOF σ JS JT ξ₀ B.ψ (-x) w = 0 from h0]
    exact map_zero (heisL σ JS JT ξ₀ B.ψ x)
  have hd : ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
      heisOF σ JS JT ξ₀ B.ψ y (heisOF σ JS JT ξ₀ B.ψ (-x) w) = heisOF σ JS JT ξ₀ B.ψ (-x) w ∨
      ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u (heisOF σ JS JT ξ₀ B.ψ (-x) w) = heisOF σ JS JT ξ₀ B.ψ (-x) w ∧
        B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
    intro y hy
    by_cases hyK : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1
    · left
      have h1 : commF σ JS JT ξ₀ B.ψ x y • heisOF σ JS JT ξ₀ B.ψ y w = w := hweig ⟨y, hy, hyK⟩
      rw [heisOF_comm, _root_.GlobalTheory.SplitVacF.commF_swap]
      conv_rhs => rw [← h1]
      exact (GlobalTheory.WeilPartsF.heisOF_smul _ _ _).symm
    · right
      push Not at hyK
      obtain ⟨k, hk, hkf, hne⟩ := hyK
      refine ⟨k, ?_, hne⟩
      rw [heisOF_comm, _root_.GlobalTheory.SplitVacF.commF_half he' hk (X.neg_mem hxX), one_smul]
      exact congrArg (heisOF σ JS JT ξ₀ B.ψ (-x)) (hspan_fix k hk hkf hwspan)
  obtain ⟨ℓ₁, hℓ₁, hℓf⟩ := GlobalTheory.HalfCoinv.exists_form (Y := Y) (ρ := heisL σ JS JT ξ₀ B.ψ)
    (B := commF σ JS JT ξ₀ B.ψ) (Θ := {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g})
    (fun x hx x' hx' f => by
      show heisOF σ JS JT ξ₀ B.ψ x (heisOF σ JS JT ξ₀ B.ψ x' f) = heisOF σ JS JT ξ₀ B.ψ (x + x') f
      rw [heisOF_heisOF, symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun f => heisOF_zero f) (fun u y f => heisOF_comm u y f) (fun u hu g hg => exists_nsmul_fix he hu hg) hφ0 hd
  have hheis := GlobalTheory.DblHeis.heisOF_dblG_deltaT_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
  obtain ⟨ℓ, h1, h2⟩ := exists_ext_form (Y := conjHalf σ e nS (nT + nT)) (ρ := heisL σ JS (dblG JT) ξ₀ B.ψ)
    (Θ := {g | IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g})
    (fun x hx x' hx' g => by
      show heisOF σ JS (dblG JT) ξ₀ B.ψ x (heisOF σ JS (dblG JT) ξ₀ B.ψ x' g) = heisOF σ JS (dblG JT) ξ₀ B.ψ (x + x') g
      rw [heisOF_heisOF, symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun g => heisOF_zero g) (fun u hu g hg => exists_nsmul_fix he hu hg)
    (dblForm ℓ₁) {p | ∃ a b, IsThetaFunOF σ JS JT ξ₀ B.ψ a ∧ IsThetaFunOF σ JS JT ξ₀ B.ψ b ∧ p = deltaT a b}
    (fun u hu p hp => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hp
      have ht : ∀ i j, cAF σ e * topR u i j = topR u i j := fun i j => hu _ _
      have hb' : ∀ i j, cAF σ e * (-botR u) i j = (-botR u) i j := fun i j => by
        show cAF σ e * -(u _ j) = -(u _ j); rw [mul_neg, hu]
      show dblForm ℓ₁ (heisOF σ JS (dblG JT) ξ₀ B.ψ u (deltaT a b)) = dblForm ℓ₁ (deltaT a b)
      have hℓ₁' : ∀ v, (∀ i j, cAF σ e * v i j = v i j) → ∀ g, IsThetaFunOF σ JS JT ξ₀ B.ψ g →
          ℓ₁ (heisOF σ JS JT ξ₀ B.ψ v g) = ℓ₁ g := fun v hv g hg => hℓ₁ v hv g hg
      rw [hheis, dblForm_deltaT, dblForm_deltaT, hℓ₁' _ ht a ha, hℓ₁' _ hb' b hb])
  refine ⟨ℓ, fun u hu g hg => h1 u hu g hg, _, _, hφ, hφ, ?_⟩
  rw [h2 _ ⟨_, _, hφ, hφ, rfl⟩, dblForm_deltaT]
  exact mul_ne_zero hℓf ((map_ne_zero _).2 hℓf)
end

noncomputable section
namespace GlobalTheory.SplitLagrF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
theorem exists_form_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ e, IsSplitIdemF σ e →
      ∀ f₀, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f₀ ≠ 0 →
      ∃ ℓ : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WOF F E nS (nT + nT), (∀ i j, cAF σ e * u i j = u i j) →
          ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
            ℓ (heisOF σ JS (dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
        (∃ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f ∧ ℓ f ≠ 0) ∧
        ∀ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det → ∃ R : ℝ, 0 < R ∧
          ∀ (f f' : WOF F E nS (nT + nT) → ℂ) (k : ℂ),
            IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
            IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f' →
            (∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
              prof σ JS JT ξ₀ B.ψ ν 𝓕 f' y = k * prof σ JS JT ξ₀ B.ψ ν 𝓕 f (M * y)) →
            ℓ f' = (R : ℂ) * k * ℓ f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  letI : MeasurableSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := borel _
  have : BorelSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := ⟨rfl⟩
  have : LocallyCompactSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := Measure.addHaar
  have : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar (G := GlobalTheory.SplitInvFormF.conjHalf σ e nS
    nT)).IsAddHaarMeasure
  have hth := GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS (nT + nT) JS
    (dblG JT) ξ₀
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS (dblG JT) ξ₀ B.ψ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f.1 y.1 ∂μ
      map_add' := fun f g => by
        rw [← integral_add (prof_integrable_k hB hS hT hξ hσξ hν h𝓕 he μ f.2)
          (prof_integrable_k hB hS hT hξ hσξ hν h𝓕 he μ g.2)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_add_k hB hν h𝓕
          f.2 g.2 y.1)
      map_smul' := fun c f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_smul ν 𝓕 c f.1 y.1) }
  obtain ⟨ℓ, hℓ0⟩ := LinearMap.exists_extend L
  have hℓ : ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
      ℓ f = ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1 ∂μ :=
    fun f hf => LinearMap.congr_fun hℓ0 ⟨f, hf⟩
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun M hM => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hu
    rw [hℓ _ (hth _ _ hf), hℓ f hf,
      GlobalTheory.SplitVacF.heisOF_add_half he (mul_mem_conjHalf _ ha) (mul_mem_conjHalf _ hb),
      ← integral_add_right_eq_self
        (fun y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1) ⟨b, hb⟩]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ = prof σ JS JT ξ₀ B.ψ ν 𝓕 f (y.1 + b)
    simp only
    rw [prof_heis_dC_k hB hS hT hξ hσξ hν h𝓕 (hth _ _ hf),
      GlobalTheory.SplitVacF.commF_half he y.2 (add_mem ha ha), one_mul,
      prof_heis_aC ν 𝓕 he f y.2 hb]
  · by_contra hall
    push Not at hall
    exact hne (lagrInt_eq_zero_k hB hS hT hξ hσξ hν h𝓕 he μ hf₀ fun u => by
      rw [← hℓ _ (hth u _ hf₀)]; exact hall _ (hth u _ hf₀))
  · obtain ⟨r, hr, hm⟩ := integral_mul_left e μ M hM
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← hm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)
end GlobalTheory.SplitLagrF
end
