module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimensionalFinitePartsWeilTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormL2Bound
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2Isometry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTransportArchimedeanSliceSobolevBounds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianInvariantFunctional
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixContinuousChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInf

/-! # ContinuousTransportFApplyK: Consolidated global theta-kernel definitions and proofs (ContinuousTransportFApplyK). -/
@[expose] public section

open UpperTheory.TP.W (GoodK)
open scoped TensorProduct Matrix
open scoped TensorProduct Matrix Classical
open Formalism.IndefR.DatumF (GAF)
open Formalism.IndefR.DatumF (IsHeckeCharF IsWeilDatumOF ResEtaF)

noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.EtaSignReal
open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU
theorem eta_eq_prod_sign_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ,
      At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  have : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  have := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [ite_eq_right (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
end GlobalTheory.EtaSignReal
end

section
abbrev _root_.GlobalTheory.T.eta_character_archimedean_formula :=
  GlobalTheory.EtaSignReal.eta_eq_prod_sign_k
end

noncomputable section
namespace GlobalTheory.HeckeExtend
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
  GlobalTheory.HeckeExtend
theorem exists_extend_hecke_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := _root_.GlobalTheory.HeckeExtend.exists_cong_ker F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := _root_.GlobalTheory.HeckeExtend.CE_isOpen F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo
  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  have : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  have : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a :=
    (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a =>
      hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz,
      GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E)
      - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
end GlobalTheory.HeckeExtend
end

section
namespace GlobalTheory.CMTraceZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem exists_ne_zero_conj_neg_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ
  : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨_, hc, _, hτ⟩ := hB.cm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push Not at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hw := hc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ w.embedding x
    rw [hall x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]
end GlobalTheory.CMTraceZero
end

section
abbrev GlobalTheory.T.exists_trace_zero_element :=
  GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k
end

section
namespace GlobalTheory.InertTensorField
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem isField_tensor_of_isInertAt_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
      IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B hB v w hvw
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [hvw]
    exact w.isPrime
  exact GlobalTheory.InertField.isField_of_inert F E hB.cm.2.2.1 v hp
end GlobalTheory.InertTensorField
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ResEtaFOfPow
open Classical in
theorem resEtaF_of_resEtaPow_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → ResEtaF χ n := by
  intro F E _ _ _ _ _ σ B hB χ n hχ
  have hcm : IsCMExt F E σ := hB.cm
  refine ⟨exists_isEtaF hcm, fun η hη a => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hη
  have hS : ∀ x ∈ normGrp F E, η x = 1 := by
    have : normGrp F E ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  have hsq : ∀ x, η x * η x = 1 := fun x => by rw [← map_mul]; exact hS _ (sq_mem_normGrp hcm x)
  have key : ∀ x, ((χ (Formalism.IndefR.DatumF.idFF F E x) : Circle) : ℂ) = if x ∈ normGrp F E then 1 else (-1) ^ n :=
    fun x => hχ x
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ normGrp F E
  · rw [ite_eq_left ha, hS a ha]; simp
  rw [ite_eq_right ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push Not at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ normGrp F E := fun hm => hb (hS b hm)
  have hab : a * b ∈ normGrp F E := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, ite_eq_right ha, ite_eq_right hbS, ite_eq_right hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
end GlobalTheory.ResEtaFOfPow
end
end

abbrev _root_.GlobalTheory.T.restricted_eta_power_character :=
  GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
theorem unit_eq_mul_conj_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
      Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E,
        algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  intro F E _ _ _ _ _ σ B hB v w hvw _hfield u hu
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [hvw]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hconj, hroot⟩ := exists_integral_gen σ hB.cm v hp
  have h2 := (hB.inert v w hvw).1
  obtain ⟨x, y, hxy⟩ := exists_int_sol v b c h2 hroot ⟨u, hu.le⟩ hu
  have hK : (x : Fv F v) ^ 2 - algebraMap F (Fv F v) (b : F) * x * y +
      algebraMap F (Fv F v) (c : F) * y ^ 2 = u := by
    have := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) hxy
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, coe_algebraMap_adicCompletionIntegers] at this
    exact this
  let ι := algebraMap (Fv F v) (Fv F v ⊗[F] E)
  have hιF : ∀ t : F, ι (algebraMap F (Fv F v) t) = (1 : Fv F v) ⊗ₜ[F] algebraMap F E t := fun t => by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  set α := (1 : Fv F v) ⊗ₜ[F] (a : E) with hα
  have hq' : α ^ 2 + ι (algebraMap F (Fv F v) (b : F)) * α + ι (algebraMap F (Fv F v) (c : F)) = 0 := by
    have := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E) hq
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, map_zero] at this
    rw [hιF, hιF]
    exact this
  have hσα : Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ α =
      -ι (algebraMap F (Fv F v) (b : F)) - α := by
    rw [hα, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hconj, hιF,
      TensorProduct.tmul_sub, TensorProduct.tmul_neg]
  refine ⟨ι x + ι y * α, ?_⟩
  rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσα]
  have hKι := congrArg ι hK
  simp only [map_add (f := _), map_sub, map_mul, map_pow] at hKι
  linear_combination (-1 : Fv F v ⊗[F] E) * hKι + ι y ^ 2 * hq'
end GlobalTheory.InertUnitNorm
end
end

noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.WeilContF
end GlobalTheory.WeilContF
namespace GlobalTheory.WeilContF
theorem exists_local_finite_parts_F_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), IsHeckeCharF χS →
        IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ
          (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ p0, ∃ N ∈ nhds p0,
                ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        om p Φ = ∑ i, pureA F (f i) (g i) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om hom Φ
    hΦ p0
  obtain ⟨pres, impl⟩ := GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀
    hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ co
    hco om hom
  obtain ⟨L₁, L₂, hL₁, hL₂, hinv⟩ := _root_.GlobalTheory.SchrFixFin.exists_fix F B.ψ hB.std.1
    κ Φ hΦ
  obtain ⟨N, hN, L₁', L₂', hL₁', hL₁c, hL₂', hNL⟩ := _root_.GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage F
    E σ nT nS JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0
  have hK := _root_.GlobalTheory.AnnCompactStd.isCompact_annihilator F B.ψ hB.std κ L₂' hL₂'
  obtain ⟨m, g, y, hg, hgy, hrep⟩ := GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition F κ L₁' hL₁' hL₁c
    _ hK
  refine ⟨N, hN, m, g, y, hg, hgy, fun p hp => ?_⟩
  have fix : ∀ x ∈ L₁', ∀ y₁ ∈ L₂', schr B.ψ (GlobalTheory.WeilCont.adeleJoin F 0 x,
      GlobalTheory.WeilCont.adeleJoin F 0 y₁) (om p Φ) = om p Φ := by
    intro x hx y₁ hy₁
    obtain ⟨x', hx', y', hy', he⟩ := hNL p hp x hx y₁ hy₁
    have := impl p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y')) Φ hΦ
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, hinv x' hx' y' hy'] at this
    change co.e (actAB (cA σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x',
      GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
      (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y₁) at he
    rw [he] at this
    exact this.symm
  refine hrep (om p Φ) (pres p Φ hΦ) ?_ ?_
  · intro x hx z
    have := congrFun (fix x hx 0 (zero_mem _)) z
    simp only [schr, adeleJoin_zero_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one,
      one_mul] at this
    exact this
  · intro z hz y₁ hy₁
    have := congrFun (fix 0 (zero_mem _) y₁ hy₁) z
    simp only [schr, adeleJoin_zero_zero, zero_dotProduct, mul_zero, add_zero,
      dotProduct_adeleJoin_zero] at this
    exact (mul_eq_right₀ hz).mp this
end GlobalTheory.WeilContF
end

section
abbrev GlobalTheory.T.weil_pair_commuting_actions :=
  GlobalTheory.WeilContF.exists_local_finite_parts_F_k

abbrev _root_.GlobalTheory.T.extend_character_to_norm_group :=
  GlobalTheory.HeckeExtend.exists_extend_hecke_k

abbrev _root_.GlobalTheory.T.inert_completion_isField :=
  GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem GlobalTheory.WeilContF.slice_bounds_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle),
        IsHeckeCharF χS → IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ,
                ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) p0 (k n : ℕ), ∃ C : ℝ,
      ∀ᶠ p in nhds p0, ∀ x : κ → mixedEmbedding.mixedSpace F,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤ C := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr Φ hΦ y
    p0 k n
  have : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  have : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  have : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hI := GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT
    rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU := GlobalTheory.T.weil_representation_pair_unitary F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS
    rT ω hω JA JB ξ hJA hJB κ co hco om htr
  obtain ⟨M, himpl, hM⟩ := _root_.GlobalTheory.ArchTransportDir.archDir_transport F E σ B.ψ nT nS JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := _root_.GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn F κ om hI.1 hU
  have hfin := GlobalTheory.T.weil_pair_commuting_actions F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT
    ω hω JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  obtain ⟨N, C, hC,
    hsob⟩ := _root_.GlobalTheory.schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq (MeasureTheory.volume : MeasureTheory.Measure (κ →
    mixedEmbedding.mixedSpace F)) k n
  choose Bd hBd using fun i j => GlobalTheory.WeilL2Words.slice_l2_of
    (_root_.GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd F B.ψ hB.std) om hI.1 M himpl hM μ hμ hiso hΦ
    p0 hfin y i j
  have hev : ∀ᶠ p in nhds p0, ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ Bd i j :=
    (Filter.eventually_all_finset _).2 fun i _ => (Filter.eventually_all_finset _).2 fun j _ => hBd i j
  refine ⟨C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), Bd i j), ?_⟩
  filter_upwards [hev] with p hp x
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F (hI.1 p Φ hΦ) y
  have hfs : (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = ⇑s := funext fun x => (hs x).symm
  rw [hfs] at hp ⊢
  refine (hsob s x).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC)
  exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hp i hi j hj
end

abbrev GlobalTheory.T.weil_pair_rational_invariance :=
  GlobalTheory.WeilContF.slice_bounds_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.WeilSchrodinger (thetaTr)
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
theorem continuous_transportF_apply_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle),
        IsHeckeCharF χS → IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ z : κ → AF F,
                Continuous fun p => om p Φ z := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
    Φ hΦ z
  have hstd := hω.std
  have hψ := hstd.1
  have hth : ∀ w, Continuous fun p => thetaTr F co B.ψ (om p Φ) w := by
    intro w
    choose g h hh hg using fun p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) =>
      GlobalTheory.T.doubled_lagrangian_intertwiner F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA
        hJB p.1 p.2
    have hθ : IsThetaFunOF σ JS JT ξ₀ B.ψ (thetaTr F co B.ψ Φ) :=
      ⟨GlobalTheory.T.doubled_lagrangian_continuous F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA
        hJB κ co hco Φ hΦ,
        GlobalTheory.T.doubled_lagrangian_unitary F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB
          κ co hco Φ hΦ,
        GlobalTheory.T.doubled_lagrangian_equivariant F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA
          hJB κ co hco Φ hΦ,
        GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA
          JB ξ hJA hJB κ co hco Φ hΦ⟩
    have hhU : ∀ p, matHomF σ JT (h p) = p.1.1 := fun p => Units.ext (hh p)
    have hgU : ∀ p, (matHomF σ JS (g p))⁻¹.1 = p.2.1.1ᵀ := by
      intro p
      apply Units.inv_eq_of_mul_eq_one_right
      change mtF σ JS (g p) * _ = 1
      rw [hg p, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
    have hcH' : Continuous fun p => matHomF σ JT (h p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JT (h p)) = fun p => p.1.1.1 := funext fun p => hh p
        rw [e]
        exact Units.continuous_val.comp (continuous_subtypeVal.comp continuous_fst)
      · have e : (fun p => (matHomF σ JT (h p))⁻¹.1) = fun p => (p.1.1)⁻¹.1 := funext fun p => by rw [hhU p]
        rw [e]
        exact Units.continuous_coe_inv.comp (continuous_subtypeVal.comp continuous_fst)
    have hcG' : Continuous fun p => matHomF σ JS (g p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JS (g p)) = fun p => ((p.2.1)⁻¹).1ᵀ := funext fun p => hg p
        rw [e]
        exact (Units.continuous_coe_inv.comp (continuous_subtypeVal.comp continuous_snd)).matrix_transpose
      · have e := funext hgU
        rw [e]
        exact (Units.continuous_val.comp (continuous_subtypeVal.comp continuous_snd)).matrix_transpose
    have hcH := continuous_induced_rng.2 hcH'
    have hcG := continuous_induced_rng.2 hcG'
    have heq : ∀ p, thetaTr F co B.ψ (om p Φ) w =
        ω (g p, h p) (thetaTr F co B.ψ Φ) w := fun p =>
      congrFun (htr p.1 p.2 (g p) (h p) (hh p) (hg p) Φ hΦ).2 w
    exact ((hω.om_cont _ hθ w).comp (hcG.prodMk hcH)).congr fun p => (heq p).symm
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    GlobalTheory.T.weil_pair_commuting_actions F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω
      JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, pureA F (f p i) (g i) := fun p hp => by
    simp only [f, dite_eq_left hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, ite_eq_left rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, ite_eq_right hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      GlobalTheory.T.weil_pair_rational_invariance F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω
        hω JA JB ξ hJA hJB κ co hco om htr
        Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.SchwartzMajorant.exists_summable_majorant F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → F) → AddChar (κ → AF F) ℂ := fun a =>
    B.ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = B.ψ ((fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
      B.ψ (⅟(2 : AF F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
    intro p y'
    simp only [thetaTr, thetaSum, Darboux.rho,
      schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.2.2.2
    refine ⟨Pi.single i (algebraMap F (AF F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF F, B.ψ (-t) * B.ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul B.ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, B.ψ (-(⅟(2 : AF F) * (z ⬝ᵥ y'))) *
          thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := _root_.GlobalTheory.CharSeriesCoef.continuousAt_coef_zero e (fun a y => hψ.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL
end GlobalTheory.WeilContF
end

abbrev GlobalTheory.T.weil_pair_central_character :=
  GlobalTheory.WeilContF.continuous_transportF_apply_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.WeilContF
theorem continuous_transportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle),
        IsHeckeCharF χS → IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsContOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
  have hfin := GlobalTheory.T.weil_pair_commuting_actions F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT
    ω hω JA JB ξ hJA hJB κ co hco om htr
  have hpt := GlobalTheory.T.weil_pair_central_character F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT
    ω hω JA JB ξ hJA hJB κ co hco om htr
  have hbd := GlobalTheory.T.weil_pair_rational_invariance F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS
    rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hpres := (GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT
    cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr).1
  refine GlobalTheory.WeilCont.isContOn_of_local F hfin (fun Φ hΦ y => ?_)
  choose s hs using fun p => GlobalTheory.WeilCont.exists_slice F (hpres p Φ hΦ) y
  refine ⟨s,
    continuous_iff_continuousAt.2 fun p0 => GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded s p0 (fun v =>
    ?_) (fun k n => ?_), hs⟩
  · simp_rw [hs]
    exact (hpt Φ hΦ _).continuousAt
  · obtain ⟨C, hC⟩ := hbd Φ hΦ y p0 k n
    refine ⟨C, hC.mono fun p hp v => ?_⟩
    have e : (⇑(s p)) = fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y) := funext (hs p)
    rw [e]
    exact hp v
end GlobalTheory.WeilContF
end
end
