module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaCmType
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQ
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianNondegenerateNegTraceZeroSmulInvSkewH
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.LatK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RestrictCoreK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplittingCharacterRestrictedEta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaSubspaceHaarIntegral
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousDualG
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.FixedOfMem
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.RowsStackRight
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.TargetDoubling
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinity
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstCoefBd
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ContinuousExpG
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefReal
public import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInj
public import Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
public import Development.WeilBound.ThetaLifts.FrameEstimates.LevelA
public import Development.WeilBound.ThetaLifts.FrameEstimates.Parity
public import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsD
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear

/-! # WpSTop: Global Weil-pair existence (`weilEx_k`) and automorphic bump-function descent. -/
@[expose] public section

noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun MeasureTheory
open Submodule (span_induction subset_span)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section
namespace PositivityTheory.ThKW.S
open scoped Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF Formalism.IndefR.LiftF
  GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF GlobalTheory.WeilSchrodinger
  GlobalTheory.WeilSchrodinger.DblTargetF GlobalTheory.WeilSchrodinger.DblTarget PositivityTheory.ThKW.Eta
  GlobalTheory.WeilTypeChar GlobalTheory.EtaCMType GlobalTheory.WeilTwistF UpperTheory.TP.W
variable {σ : E →ₐ[F] E} {B : Base F E}
private theorem exists_eta_pk (hB : GoodK σ B) :
    ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) ∧ UnramInert σ η := by
  have : IsCMField E := isCMField_of_cmExt hB.cm
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ⟨ξ, hξ, hξe⟩ : ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
    obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
    have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
    obtain ⟨U, hU, hUinf, hUk⟩ := _root_.GlobalTheory.OpenCongrIdele.exists_open_congr F E q hq.ne_zero
    obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
      (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
      (fun _ => by simp) (fun k hk => by
        obtain ⟨u, hu, hu1⟩ := hUk k hk
        refine Units.ext ?_
        rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
        have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
            (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
          rw [hu]; exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
        simp only [e]
        exact (_root_.GlobalTheory.weil_unit_phase_prod F E σ hB.cm B.emb q hq
          (by omega) ht u hu1).symm)
    refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1,
      ⟨Continuous.subtype_mk (Units.continuous_val.comp hχc) _, fun k => Circle.ext <| by
        show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1; rw [hχk]; rfl⟩,
      fun z hz => by show ((χ z : ℂˣ) : ℂ) = _; rw [hχU z (hUinf z hz), chiInf_apply]; simp⟩
  have ⟨η, h1, h2, h3⟩ : ∃ η : (AF F ⊗[F] E)ˣ →* Circle,
      IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
    obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
    let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
    have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun _ => rfl
    have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := fun a ha => by
      have e3 : ξ (idFF F E a) = η₀ a := Circle.ext <| by
        rw [hξe _ (at_idFF a ha), GlobalTheory.T.eta_character_archimedean_formula F E σ B hB η₀ hη₀ a ha]
        exact Finset.prod_congr rfl fun _ _ => zpow_one _
      rw [hlam, e3, mul_inv_cancel]
    obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := GlobalTheory.T.extend_character_to_norm_group F E σ B hB lam
      ((hξ.1.comp continuous_idFF).mul hη₀.1.inv)
      (fun a => by rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]) hlinf
    refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => by
        change ξ _ * (lam' _)⁻¹ = 1; rw [hξ.2, hl'H.2, inv_one, one_mul]⟩,
      ⟨⟨η₀, hη₀⟩, fun η hη a => by
        change ξ _ * (lam' _)⁻¹ = _
        rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]⟩,
      fun z hz => by change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _; rw [hl'inf z hz, inv_one, mul_one]; exact hξe z hz⟩
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ), 2 * (u : Fv F v) ∈ v.adicCompletionIntegers F →
      2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F →
      u ∈ GlobalTheory.QuadSymbol.normGroup F E (Fv F v) := by
    intro v u hu1 hu2
    obtain ⟨δ, b, _, hb0, hb1, hbb⟩ :=
      GlobalTheory.QuadNormBase.exists_basis F E σ hB.cm.2.2.1 (sig_invol hB.cm) (sig_ne hB.cm)
    refine (GlobalTheory.QuadSymbol.mem_normGroup_iff_form b hb0 hbb).2 ?_
    rcases GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
    · have hs : τ (b 1) * τ (b 1) = algebraMap F (Fv F v) δ := by rw [← map_mul, hbb, AlgHom.commutes]
      have hs0 : τ (b 1) ≠ 0 := (map_ne_zero τ).2 (b.ne_zero 1)
      have h20 : (2 : Fv F v) ≠ 0 := by rw [← map_ofNat (algebraMap F (Fv F v)) 2]; exact (map_ne_zero _).2 two_ne_zero
      refine ⟨((u : Fv F v) + 1) / 2, ((u : Fv F v) - 1) / (2 * τ (b 1)), ?_⟩
      rw [← hs]; field_simp; ring
    · have hv2 : Valued.v (2 : Fv F v) = 1 := by
        rw [show (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) by rw [map_ofNat, map_ofNat]]
        refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans
          (le_antisymm (v.valuation_le_one 2) (not_lt.1 fun h =>
            (hB.inert v w hw).1 ((v.valuation_lt_one_iff_mem 2).1 h)))
      have a1 : Valued.v (2 * (u : Fv F v)) ≤ 1 := hu1
      have a2 : Valued.v (2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v)) ≤ 1 := hu2
      rw [map_mul, hv2, one_mul] at a1 a2
      have hu : Valued.v (u : Fv F v) = 1 := le_antisymm a1 <| by
        have hm := congrArg Valued.v u.mul_inv; rw [map_mul, map_one] at hm; rw [← hm]
        exact mul_le_of_le_one_right' a2
      obtain ⟨z, hz⟩ := GlobalTheory.InertUnitNorm.unit_eq_mul_conj_k F E σ B hB v w hw
        (GlobalTheory.T.inert_completion_isField F E σ B hB v w hw) u hu
      obtain ⟨x, y, rfl⟩ := tensor_decomp (A := Fv F v) (b 1) (fun x => ⟨b.repr x 0, b.repr x 1, by
        have hx := b.sum_repr x; rw [Fin.sum_univ_two, hb0] at hx; exact hx.symm⟩) z
      refine ⟨x, y, tensor_inj (F := F) (E := E) ?_⟩
      have e1 : ((1 : Fv F v) ⊗ₜ[F] b 1) * ((1 : Fv F v) ⊗ₜ[F] b 1) =
          algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) δ) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb, ← IsScalarTower.algebraMap_apply,
          Algebra.TensorProduct.algebraMap_apply']
      rw [hz, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, hb1, TensorProduct.tmul_neg, map_sub, map_mul, map_pow, map_pow, ← e1]; ring
  have hk : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ UI σ,
      x ∈ ((Units.map (incAF F E).toMonoidHom).range ⊔ (idFF F E).range) ⊔ WE F E N → η x = 1 := by
    obtain ⟨M, hM, hMk⟩ := PositivityTheory.ThKW.Eta.exists_level η h1.1
    obtain ⟨N, hN, hNk⟩ := exists_sep B.v₁
    refine ⟨M * N, Nat.mul_pos hM hN, fun x hx hV => ?_⟩
    obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.1 hV
    obtain ⟨_, ⟨k, rfl⟩, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
    obtain ⟨f, hf⟩ := (_root_.GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hB.cm).2 k
      (fixed_of_mem hB.cm B.τ₁ hNk hx hw k a hyw)
    have hf0 : f ≠ 0 := by rintro rfl; rw [map_zero] at hf; exact k.ne_zero hf.symm
    let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
    have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := Units.ext <| by
      show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
      rw [← hf, incAF_algebraMap]
    rw [hinc, ← map_mul] at hyw
    generalize fU * a = a' at hyw
    have e1 : idFF F E a' = x * w⁻¹ := by rw [← hyw, mul_inv_cancel_right]
    have e2 : idFF F E a'⁻¹ = x⁻¹ * w := by rw [map_inv, e1, mul_inv, inv_inv]
    have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hB.cm.2.2.1 }
    have hint : ∀ t : AF F, algebraMap (AF F) (AF F ⊗[F] E) t ∈ SE F E → ∀ v : HeightOneSpectrum (𝓞 F),
        2 * t.2 v ∈ v.adicCompletionIntegers F := fun t ht v => by
      have hfm := _root_.GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF F E 1 t (CE_one ht)
      rw [hB.cm.2.2.1] at hfm
      obtain ⟨c, hc, e⟩ := hfm
      have ev : evalV F v (2 • t.2) = evalV F v (1 • c) := congrArg (evalV F v) e
      rw [one_smul, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat] at ev
      exact ev.symm ▸ hc v
    have h1' : η (idFF F E (finU F (sndU F a'))) = 1 := by
      have ha1 : (idFF F E a' : AF F ⊗[F] E) ∈ SE F E := by rw [e1]; exact SE_mul hx.2.2.1 (mem_SE_of_CE hw.2)
      have ha2 : (idFF F E a'⁻¹ : AF F ⊗[F] E) ∈ SE F E := by rw [e2]; exact SE_mul hx.2.2.2 (mem_SE_of_CE hw.1)
      obtain ⟨z, hz⟩ := (GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm E (finU F (sndU F a'))).2
        ⟨fun v => hloc v _ (hint _ ha1 v) (hint _ ha2 v),
         fun w => by
           rw [show GlobalTheory.IdeleNormChar.infComp (finU F (sndU F a')) w = 1 from Units.ext rfl]
           exact one_mem _⟩
      obtain ⟨⟨η₀, h0⟩, h⟩ := h2
      rw [h η₀ h0, ← hz, h0.2.2.1 z, one_pow]
    let p : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cut (fI F E) fI_idem)
    have hp : ∀ z : (AF F ⊗[F] E)ˣ, (p z : AF F ⊗[F] E) = (1 - fI F E) + fI F E * z := fun _ => rfl
    have px : p x = x := Units.ext (by
      have h1x : (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E := hx.1; rw [hp]; linear_combination -h1x)
    have pa : p (idFF F E a') = idFF F E (finU F (sndU F a')) := Units.ext (by
      rw [hp]
      show 1 - algebraMap (AF F) (AF F ⊗[F] E) (uFin F) + algebraMap (AF F) (AF F ⊗[F] E) (uFin F) *
        algebraMap (AF F) (AF F ⊗[F] E) (a' : AF F) = algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 (a' : AF F).2)
      rw [← map_mul, ← map_one (algebraMap (AF F) (AF F ⊗[F] E)), ← map_sub, ← map_add (f := _), uFin_mul]
      exact congrArg _ (Prod.ext (by show (1 : Ainf F) - 0 + 0 = 1; simp)
        (by show (1 : Af F) - 1 + (a' : AF F).2 = (a' : AF F).2; simp)))
    have pC : ∀ z : (AF F ⊗[F] E)ˣ, (z : AF F ⊗[F] E) - 1 ∈ CE F E (M * N) → (p z : AF F ⊗[F] E) - 1 ∈ CE F E M :=
      fun z hz => by
        obtain ⟨s, hs, e⟩ := mem_CE.1 (CE_mul hz)
        exact mem_CE.2 ⟨fI F E * s, SE_mul fI_mem hs, by rw [← mul_smul_comm, e, hp]; ring⟩
    have h2' : η (p w) = 1 := hMk _ ⟨pC w hw.1, by rw [← map_inv]; exact pC _ hw.2⟩ <| by
      show (1 - fI F E) * (p w : AF F ⊗[F] E) = 1 - fI F E
      rw [hp]; linear_combination (1 - (w : AF F ⊗[F] E)) * (fI_idem (F := F) (E := E))
    rw [← px, ← hyw, map_mul, map_mul, pa, h1', h2', mul_one]
  obtain ⟨N, hN, hk⟩ := hk
  obtain ⟨ν, hV, hU⟩ := exists_ext _ _ η hk
  have hW : ∀ z ∈ WE F E N, ν z = 1 := fun z hz => hV z (Subgroup.mem_sup_right hz)
  have hWo : IsOpen (WE F E N : Set (AF F ⊗[F] E)ˣ) :=
    ((CE_isOpen F E N hN).preimage (Units.continuous_val.sub continuous_const)).inter
      ((CE_isOpen F E N hN).preimage (Units.continuous_coe_inv.sub continuous_const))
  have hν : Continuous ν := continuous_of_continuousAt_one _ <| by
    rw [ContinuousAt, map_one]
    exact tendsto_const_nhds.congr' (by filter_upwards [hWo.mem_nhds (one_mem _)] with z hz; exact (hW z hz).symm)
  refine ⟨η * ν⁻¹, ⟨h1.1.mul hν.inv, fun x => by
      change η _ * (ν _)⁻¹ = 1
      rw [h1.2, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨x, rfl⟩)), inv_one, one_mul]⟩,
    ⟨h2.1, fun e he a => by
      change η _ * (ν _)⁻¹ = _
      rw [h2.2 e he, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, rfl⟩)), inv_one, mul_one]⟩,
    fun z hz => by
      change ((η z * (ν z)⁻¹ : Circle) : ℂ) = _
      have hzW : z ∈ WE F E N := ⟨mem_CE_of_atInf F E _ hN _ hz, mem_CE_of_atInf F E _ hN _ fun u hu => by
        have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 =
            -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
          rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
        rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]⟩
      rw [hW z hzW, inv_one, mul_one]; exact h3 z hz,
    fun x a b c d => by
      change η _ * (ν _)⁻¹ = 1
      have hx : x ∈ UI σ := ⟨by
        show (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E
        rw [← sub_eq_zero, ← mul_sub_one]
        exact adele_tensor_ext _ (by rw [map_mul, map_sub _ (x : AF F ⊗[F] E), a, map_one, sub_self, mul_zero])
          (by rw [map_mul, map_sub, map_one, fin_fI, sub_self, zero_mul]), b, mem_SE_of_fin c, mem_SE_of_fin d⟩
      rw [hU x hx, mul_inv_cancel]⟩

private theorem exists_isWeilDatumOF_pk (hB : GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hξσ : σ ξ₀ = -ξ₀) (hLat : PositivityTheory.ThKW.LatH σ JS JT ξ₀) {χS χT : (AF F ⊗[F] E)ˣ →* Circle}
    (hcS : IsHeckeCharF χS) (hcT : IsHeckeCharF χT) (rS : ResEtaF χS nS) (rT : ResEtaF χT nT) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω := by
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := exists_eta_pk hB
  obtain ⟨Λ, hΛ1, hΛ2⟩ := hLat
  have hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ :=
    GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀
  obtain ⟨w, lam, Om, hO⟩ := latK F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc
  obtain ⟨om, ho⟩ := datumK_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc w lam Om hO η hη1 hη2 hη3 hη4
  let νS := (η ^ nS)⁻¹ * χS
  let νT := (η ^ nT)⁻¹ * χT
  have hνS := isHeckeCharF_div_pow hcS hη1 nS
  have hνT := isHeckeCharF_div_pow hcT hη1 nT
  have rνS := resEtaF_div_pow rS hη2
  have rνT := resEtaF_div_pow rT hη2
  obtain ⟨a, aval, arat, acont⟩ := exists_muF (σ := σ) hB.cm hB.unram hS.2 νT⁻¹ (heckeF_inv hνT)
    (fun t => by rw [MonoidHom.inv_apply, triv_of_resEtaF rνT, inv_one])
  obtain ⟨b, bval, brat, bcont⟩ := exists_muF (σ := σ) hB.cm hB.unram hT.2 νS hνS (triv_of_resEtaF rνS)
  let om' : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ) :=
    { toFun := fun p => ((a p.1 * b p.2 : Circle) : ℂ) • om p
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, smul_mul_smul_comm, Circle.coe_mul]; congr 1; ring }
  have happ : ∀ p f, om' p f = ((a p.1 * b p.2 : Circle) : ℂ) • om p f := fun _ _ => rfl
  have hom' : IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS * νS) (η ^ nT * νT) om' :=
    ⟨ho.std, heckeF_mul ho.hecS hνS, heckeF_mul ho.hecT hνT, resEtaF_mul ho.resS rνS, resEtaF_mul ho.resT rνT,
      fun p f hf => happ p f ▸ thetaOF_smul _ (ho.om_pres p f hf),
      fun g h w₀ f hf => by rw [happ, happ, heisOF_smul, ho.om_heis g h w₀ f hf],
      fun γ hγ γ' hγ' f hf => by
        rw [happ]; change ((a γ * b γ' : Circle) : ℂ) * om (γ, γ') f 0 = f 0
        rw [arat γ hγ, brat γ' hγ', mul_one, Circle.coe_one, one_mul]; exact ho.om_aut γ hγ γ' hγ' f hf,
      fun f hf w => (continuous_subtypeVal.comp ((acont.comp continuous_fst).mul (bcont.comp continuous_snd))).mul
        (ho.om_cont f hf w),
      fun μ 𝓕 hμ h𝓕 p f hf => by
        rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
        refine lintegral_congr fun w => ?_
        have hn : ‖om' p f w‖ = ‖om p f w‖ := by
          rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
        rw [← ofReal_norm, ← ofReal_norm, hn],
      fun e he g h hg hh x y hx hy => by
        obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
        refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
        rw [happ, map_smul, H ℓ hℓ f hf, aval g x (root_of_detAt hS.2 he g hg x hx),
          bval h y (root_of_detAt hT.2 he h hh y hy), MonoidHom.inv_apply]
        simp only [splitFacOF, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]; ring⟩
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩

private theorem mk_split_pk (hB : GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hσ : σ ξ₀ = -ξ₀) {χS χT : (AF F ⊗[F] E)ˣ →* Circle} (cS : IsHeckeCharF χS) (cT : IsHeckeCharF χT)
    (rS : ResEtaF χS nS) (rT : ResEtaF χT nT) {ω}
    (hω : IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω)
    {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E} {ξ : AF F ⊗[F] E}
    (hA : JA = JTᵀ) (hBm : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
      IsTransportF σ B.ψ co ω om ∧ IsUSplitting (adeleClass F) B.ψ co (actAB (cA σ)) om ∧
      IsContOn (adeleClass F) om := by
  obtain ⟨om, hom⟩ := GlobalTheory.TransportF.exists_isTransportF_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT
    rS rT ω hω JA JB ξ hA hBm κ co hrat
  have k2 := GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT
    ω hω JA JB ξ hA hBm κ co hrat om hom
  have k3 := GlobalTheory.WeilAdmCM.transport_admissible_weil_datum F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS
    rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have k4 := GlobalTheory.T.weil_representation_pair_unitary F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω
    hω JA JB ξ hA hBm κ co hrat om hom
  have k5 := GlobalTheory.WeilContF.continuous_transportF_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω
    hω JA JB ξ hA hBm κ co hrat om hom
  exact ⟨om, hom, ⟨⟨k2.1, k2.2, k3⟩, k4, k5⟩, k5⟩

private theorem exists_dbl_target_pk (hB : GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hJS : IsHermND σ JS) (hJT : IsHermND σ JT) {ξ₀ : E} (hξ0 : ξ₀ ≠ 0)
    (hσξ : σ ξ₀ = -ξ₀) (hLat : PositivityTheory.ThKW.LatH σ JS JT ξ₀) {χS χT : (AF F ⊗[F] E)ˣ →* Circle}
    (hS : IsHeckeCharF χS) (hT : IsHeckeCharF χT) (rS : ResEtaF χS nS) (rT : ResEtaF χT nT) {ω}
    (hω : IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω)
    {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E} {ξ : AF F ⊗[F] E}
    (hA : JA = JTᵀ) (hBm : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    {om} (hom : IsTransportF σ B.ψ co ω om) :
    ∃ (dd : Darboux (symp (cA σ) ξ (incM F JB) (dbl (incM F JA))) (κ ⊕ κ))
      (omd : UG (cA σ) (dbl (incM F JA)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
      IsDblCoord (cA σ) ξ (incM F JB) (incM F JA) (transD (cA σ) co) dd ∧
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (dbl (incM F JA)) dd χS (diagCols (Fin nT)) omd ∧
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (dbl (incM F JA))),
        gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  have hJTd := isHermND_dblG hJT
  have h1 := isHeckeCharF_one (F := F) (E := E)
  have r1 := resEtaF_one_dbl hB.cm.2.2.1 rT
  obtain ⟨ωd, hωd⟩ := exists_isWeilDatumOF_pk hB hJS hJTd hξ0 hσξ (PositivityTheory.ThKW.LatH.dblT hLat) hS h1 rS r1
  have hrat' := coDbl_rat hA co hrat
  obtain ⟨omp, hmp, hsp, _⟩ := mk_split_pk hB hJS hJTd hξ0 hσξ hS h1 rS r1 hωd rfl hBm (coDbl hA co) hrat'
  have hsg := GlobalTheory.T.splitting_character_restricted_eta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS hS rS JB ξ
    hBm (κ ⊕ κ) (coDbl hA co) hrat' ωd hωd omp hmp
  have t4 := isUSplitting_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM hA) (isUSplitting_inl hsp)
  have t5 := siegelRule_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM hA) χS _ hsg
  refine ⟨_, _, isDblCoord_transD co, ⟨isLagr_diagCols _ _, t4, t5⟩, ?_⟩
  intro g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have key := GlobalTheory.T.doubled_weil_apply_boxFun_eq_boxFun_left F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS
    χT hS hT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom ωd hωd omp hmp g (ugDbl hA gd)
    (by rw [GlobalTheory.WeilSchrodinger.DblTargetF.ugDbl_coe, hgd]) φ₁ hφ₁ φ₂ hφ₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply]; exact key

theorem weilEx_k : PositivityTheory.ThKG.Tow.WeilEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW M hM χX χW hcX hcW rX rW
  obtain ⟨ξ₀, hξ, hσξ⟩ := GlobalTheory.T.exists_trace_zero_element F E σ B hB
  have hXu := _root_.GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hX
  have hWu := _root_.GlobalTheory.SkewUnit.isUnit_det_of_isSkew F E σ B d W r' s' hW
  have hT : IsHermND σ X.Jᵀ := ⟨fun i j => by simpa using hX.herm j i, by rw [Matrix.det_transpose]; exact hXu.ne_zero⟩
  have hS : IsHermND σ (-ξ₀ • W.J⁻¹) := _root_.GlobalTheory.skew_dual_isHermND F E
    σ d W.J hW.skew hWu ξ₀ hξ hσξ
  have hLat : PositivityTheory.ThKW.LatH σ (-ξ₀ • W.J⁻¹) X.Jᵀ ξ₀ := PositivityTheory.ThKW.latH_of hB.cm hX hW hXu hWu hξ
  have rW' := GlobalTheory.T.restricted_eta_power_character F E σ B hB χW d rW
  have rX' := GlobalTheory.T.restricted_eta_power_character F E σ B hB χX n rX
  obtain ⟨ω, hω⟩ := exists_isWeilDatumOF_pk hB hS hT hξ hσξ hLat hcW hcX rW' rX'
  have eB : (-1 : AF F ⊗[F] E) • incM F W.J = incM F (ξ₀ • (-ξ₀ • W.J⁻¹)⁻¹) := by
    have e1 : (-ξ₀ • W.J⁻¹)⁻¹ = (-ξ₀)⁻¹ • W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hWu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : ξ₀ • (-ξ₀)⁻¹ • W.J = -W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    rw [e1, e2]; funext i j; simp [incM]
  obtain ⟨om, hom, hsp, h5⟩ := mk_split_pk hB hS hT hξ hσξ hcW hcX rW' rX' hω (by simp) eB M.co hM.rat
  have h7 := exists_dbl_target_pk hB hS hT hξ hσξ hLat hcW hcX rW' rX' hω (by simp) eB M.co hM.rat hom
  have h6 : ∃ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
      (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd ∧
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX
        (diagCols (Fin d)) omd ∧
      ∀ (g : UG (cA σ) (incM F W.J)) (gd : UG (cA σ) (dbl (incM F W.J))),
        gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d),
          omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂ := by
    open PositivityTheory.ThKW.Sw in
    have lS := invT_mul hS
    have lT := invT_mul hT
    have hsm : ∀ {m : ℕ} (N : Matrix (Fin m) (Fin m) E), incM F (ξ₀ • N) = incAF F E ξ₀ • incM F N := fun N => by
      ext i j; exact map_mul (incAF F E) _ _
    have hB' : (-1 : AF F ⊗[F] E) • incM F W.J = incAF F E ξ₀ • incM F (-ξ₀ • W.J⁻¹)⁻¹ := eB.trans (hsm _)
    have hx : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 _ hξ).map _
    have hd : IsUnit (incM F (-ξ₀ • W.J⁻¹)⁻¹).det := by
      have h2 : (incM F (-ξ₀ • W.J⁻¹)⁻¹).det = incAF F E ((-ξ₀ • W.J⁻¹)⁻¹).det := (RingHom.map_det (incAF F E) _).symm
      rw [h2]; exact (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).map _
    have hle := ug_le (cA σ) hB' hx hd
    have hge := ug_ge (cA σ) hB' hx
    have hD := smul_dbl hB'
    have hge' := ug_ge (cA σ) hD hx
    have htr := swap_transport σ lS lT B.ψ hle M.co _ (castD_transD_rho _ hB' M.co B.ψ) hom (swapHom hle om)
      (swapHom_apply hle om)
    have hrat' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
        (castD _ hB' (transD (cA σ) M.co)).e (incM F x) =
          (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
      obtain ⟨y, z, h⟩ := hM.rat xᵀ; exact ⟨y, z, (castD_transD_e _ hB' M.co _).trans h⟩
    have g1 : (-ξ₀ • W.J⁻¹)⁻¹ = ((-ξ₀ • W.J⁻¹)⁻¹ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
    have g2 : incAF F E ξ₀ • incM F X.J = incM F (ξ₀ • (X.Jᵀ⁻¹ᵀ)⁻¹) := by
      rw [(dual_inv lT).2, hsm]; simp
    obtain ⟨dd, omd, k1, k2, k3⟩ := exists_dbl_target_pk hB (isHermND_invT hT) (isHermND_invT hS) hξ hσξ
      (PositivityTheory.ThKW.LatH.swap hS hT hLat) hcX hcW rX' rW' (swap_datum σ lS lT ξ₀ B.ψ hω) g1 g2 _ hrat' htr
    refine ⟨castD₂ _ hD dd, omd.comp (Subgroup.inclusion hge'), isDblCoord_cast₂ _ hB' M.co k1,
      isUWeilSplit_cast₂ _ hD hge' (isLagr_diagCols _ _) k2, fun g gd hgd φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
    have k4 := k3 (Subgroup.inclusion hge g) (Subgroup.inclusion hge' gd) hgd φ₁ hφ₁ φ₂ hφ₂
    exact k4.trans (congrArg (fun u => boxFun (u φ₁) φ₂) (swapHom_apply hle om _ 1))
  exact ⟨om, ⟨isUSplitting_inr hsp, h6⟩, ⟨transD _ M.co, transD_e M.co, isUSplitting_inl hsp, h7⟩, h5⟩
end PositivityTheory.ThKW.S
end

section
open scoped NNReal
open Filter Topology GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels hiding pure
open GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open GlobalTheory.UnitaryBC (RU finU IsAutFormU)

namespace UpperTheory.TP

variable {σ : E →ₐ[F] E}
variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
variable {χX χW : Chr F E} {om : Rep σ X W}

private theorem lift_equiv_pk (T : Tools_k) (hp : IsPair_k B M χX χW om n 0 d 0) {Φ : Fn F n d}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) {φ : UA σ X.J → ℂ} (hφ : IsFn φ) (a : UA σ X.J) (b h : UA σ W.J) :
    lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = lift M om Φ φ (h * b) := by
  have c : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have hTB := T.basic F E σ B n d X W M χX χW om n 0 d 0 hp
  let G : UA σ X.J → ℂ := fun x => theta om Φ x (h * b) * star (φ x)
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, G (γ * x) = G x := fun γ hγ x => by
    have h1 := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (h * b)
    rw [one_mul] at h1; simp only [G]; rw [h1, hφ.2 γ hγ x]
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have := hp.good.haar; have : M.μ.IsMulRightInvariant := c.right _ hp.good.haar; have := c.cnt
  have : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  have : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ := ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = ∫ x in M.dom, G (x * a) ∂M.μ :=
    integral_congr_ae (.of_forall fun x => by simp only [G, theta]; rw [← mul_apply_eq_comp, ← map_mul]; rfl)
  have h1 := (measurePreserving_mul_right M.μ a).setIntegral_preimage_emb (measurableEmbedding_mulRight a) G
    ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom)
  rw [show (fun x : UA σ X.J => x * a) ⁻¹' ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) = M.dom by ext; simp] at h1
  have hfd : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ a⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id (fun γ x => mul_assoc γ.1 x a⁻¹)
  rw [hL, h1, hfd.setIntegral_eq hp.good.dom (f := G) (fun γ x => hinv γ.1 γ.2 x)]; rfl

private theorem lift_lin_pk (T : Tools_k) (hP : IsPair_k B M χX χW om n 0 d 0) :
    (∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ →
      lift M om (Φ + Φ') φ = lift M om Φ φ + lift M om Φ' φ) ∧
    (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ →
      lift M om (c • Φ) φ = c • lift M om Φ φ) ∧
    (∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ φ' : UA σ X.J → ℂ, IsFn φ → IsFn φ' →
      lift M om Φ (φ + φ') = lift M om Φ φ + lift M om Φ φ') ∧
    (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ →
      lift M om Φ (c • φ) = (starRingEnd ℂ) c • lift M om Φ φ) := by
  have hint : ∀ {Φ : Fn F n d}, Φ ∈ schA F (Fin n × Fin d) → ∀ {φ : UA σ X.J → ℂ}, IsFn φ → ∀ h : UA σ W.J,
      IntegrableOn (fun g => theta om Φ g h * star (φ g)) M.dom M.μ := fun {Φ} hΦ {φ} hφ h => by
    have hc : Cpt σ X.J := T.cpt F E σ B n X n 0 hP.base (Or.inl hP.herm) (by simp)
    obtain ⟨h1, h2, -⟩ := (T.basic F E σ B n d X W M χX χW om n 0 d 0 hP).1 Φ hΦ
    have hcont : Continuous fun g => theta om Φ g h * star (φ g) :=
      (h1.comp (continuous_id.prodMk continuous_const)).mul (continuous_star.comp hφ.1)
    obtain ⟨C, hC⟩ := hc.bdd hcont fun γ hγ g => by
      have e := h2 γ hγ 1 (one_mem _) g h; rw [one_mul] at e; simp only [e, hφ.2 γ hγ g]
    exact Measure.integrableOn_of_bounded (M := C) (hc.fin M.μ M.dom hP.good.haar hP.good.dom).ne
      hcont.aestronglyMeasurable (Eventually.of_forall hC)
  have hpres := hP.weil.isUSplitting.pres
  refine ⟨fun Φ hΦ Φ' hΦ' φ hφ => funext fun h => ?_, fun c Φ hΦ φ hφ => funext fun h => ?_,
    fun Φ hΦ φ φ' hφ hφ' => funext fun h => ?_, fun c Φ hΦ φ hφ => funext fun h => ?_⟩
  · have e : ∀ g, theta om (Φ + Φ') g h * star (φ g) = theta om Φ g h * star (φ g) + theta om Φ' g h * star (φ g) :=
      fun g => by rw [show theta om (Φ + Φ') g h = theta om Φ g h + theta om Φ' g h by
        simp only [theta, map_add (f := _)]; exact thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΦ'), add_mul]
    simp only [lift, Pi.add_apply, e]; exact integral_add (hint hΦ hφ h) (hint hΦ' hφ h)
  · simp only [lift, Pi.smul_apply, smul_eq_mul, show ∀ g, theta om (c • Φ) g h * star (φ g) =
      c * (theta om Φ g h * star (φ g)) from fun g => by simp only [theta, map_smul, thetaSum_smul, mul_assoc],
      integral_const_mul]
  · simp only [lift, Pi.add_apply, star_add, mul_add]
    exact integral_add (hint hΦ hφ h) (hint hΦ hφ' h)
  · simp only [lift, Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
    rw [show (fun g => theta om Φ g h * (star c * star (φ g))) =
      fun g => star c * (theta om Φ g h * star (φ g)) from funext fun _ => by ring, integral_const_mul]

private theorem pol_arch_pk (hp : IsPair_k B M χX χW om n 0 d 0) {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F))
    {h : UA σ W.J} (hh : h ∈ UAt σ W (evI F)) {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) : om (g, h) Φ ∈ PolData B M := by
  obtain ⟨T, hT, hP⟩ := PositivityTheory.ThKF.A.archOp_k F E σ B n d X W M χX χW om n 0 d 0 hp g hg h hh
  have kg : g ∈ KInf σ X B.emb := ⟨hg, fun w => by
    rw [Prs.cartan_one (hp.herm.sig w) (hp.herm.cartan w)]; exact Commute.one_right _⟩
  have kh : h ∈ KInf σ W B.emb := ⟨hh, fun w => by
    rw [Prs.cartan_one (hp.skew.sig w) (hp.skew.cartan w)]; exact Commute.one_right _⟩
  refine span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun _ _ _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c _ _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, f1, φ, f2, f3, rfl⟩
  obtain ⟨ξ, hξ, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good φ f2 f3
  rw [e f, hT.1 f ξ hξ, ← e (T f)]
  exact subset_span ⟨T f, hP kg kh f f1, φ, f2, f3, rfl⟩

private theorem pol_fin_pk (T : Tools_k) {r s r' s' : ℕ} (hp : IsPair_k B M χX χW om r s r' s') (v : Pl F)
    {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v))
    {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) : om (g, h) Φ ∈ PolData B M := by
  classical
  refine span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun _ _ _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c _ _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, hf, φ, hSB, hcof, rfl⟩
  obtain ⟨φ₁, ⟨s1, a1⟩, -⟩ := (T.acts F E σ B n d X W M χX χW om r s r' s' hp v).1 g hg h hh (φ v) (hSB v)
  have e := (PositivityTheory.ThKF.pureAct F _ v (om (g, h)) f φ hSB
    ((hcof.and hp.good.std).mono fun _ k => k.1.trans k.2)).2.2 φ₁ a1
  refine e ▸ subset_span ⟨f, hf, Function.update φ v φ₁, fun u => ?_,
    (hcof.and ((Set.finite_singleton v).compl_mem_cofinite)).mono fun u k => by
      rw [Function.update_of_ne k.2, k.1], by congr!⟩
  by_cases hu : u = v
  · subst hu; simpa using s1
  · simpa [Function.update_of_ne hu] using hSB u

private theorem levelX_pure_pk {r s r' s' : ℕ} (hp : IsPair_k B M χX χW om r s r' s')
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) :
    ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) →
      ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = pureA F f φ := by
  open PositivityTheory.ThKEst PositivityTheory.ThKEst.levelStructure PositivityTheory.ThKEst.LatticeQuotientMeasure
    PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi in
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun _ _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) :=
    fun f => Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := coefBd_of_k coefReal_of F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have := ring_AE F E
  have h1 : ∀ᶠ u in 𝓝 (1 : UA σ X.J), levelStructure.IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) →
      ∀ f, schr B.ψ (M.co.e (mat u * z)) (pureA F f φ) = schr B.ψ (M.co.e z) (pureA F f φ) := by
    have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
    have hV := schr_near hp.base.std hφ (hCc.image he)
    have hm : Continuous fun q : UA σ X.J × Ten F E n d => M.co.e ((mat q.1 - 1) * q.2) :=
      he.comp ((((Units.continuous_val.comp continuous_subtypeVal).comp continuous_fst).sub continuous_const).matrix_mul
        continuous_snd)
    have h1' := hCc.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ X.J))
      (P := fun u c => M.co.e ((mat u - 1) * c) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
        rwa [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, Matrix.zero_mul, map_zero])
    filter_upwards [h1'] with u h1' hu z ⟨c, hc, hz⟩ f
    rw [at_iff, smul_sub, sub_eq_zero] at hz
    have hu' : e0 F • (mat u - 1) = mat u - 1 := hu
    have e : mat u * z = z + (mat u - 1) * c := by
      have e1 : (mat u - 1) * c = (mat u - 1) * z := by
        rw [← hu', Matrix.smul_mul, ← Matrix.mul_smul, ← hz, Matrix.mul_smul, Matrix.smul_mul]
      rw [e1, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
    rw [e, map_add (f := _)]
    exact h1' c hc (by rw [← map_smul, ← Matrix.smul_mul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f
  have hi : Continuous fun u : UA σ X.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin n) (AE F E))).comp continuous_subtypeVal).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ X.J => ‖om (u, 1) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_id.prodMk continuous_const)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, one_apply_eq_self, div_self hy]; norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x,
      om (u, 1) (pureA F f φ) x * (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := fun f x => by
    refine fourierInj_of F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀))
      _ (mem f) _ (mem f₀) ?_ x y
    funext w; obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [coefEq_of_k F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀),
      ParityOfCoefficients.mat_one_inv, Matrix.transpose_one, Matrix.mul_one]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold PositivityTheory.ThKEst.coef; rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (mat u⁻¹ * z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [← h1 hu _ a', ← Matrix.mul_assoc, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.one_mul]
    have b := hb f f₀ z; have b' := hb f f₀ (mat u⁻¹ * z)
    rw [maj, ite_eq_right a, mul_zero, norm_le_zero_iff] at b
    rw [maj, ite_eq_right a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y; rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this; exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (u ^ k, 1) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((u ^ k * u, 1) : UA σ X.J × UA σ W.J) = (u ^ k, 1) * (u, 1) from by simp, map_mul,
        mul_apply_eq_comp, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near c fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f; rw [hc, h6, one_smul]

open PositivityTheory.ThKEnd.Grp in
private theorem stab_of_pk {m : ℕ} {Y : Spc F E m} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (A : UA σ Y.J →* Module.End ℂ V) (P : Submodule ℂ V)
    (hlev : ∀ Φ ∈ P, ∀ᶠ u in 𝓝 (1 : UA σ Y.J), (∀ w, (mat u).map (piInf (τ w)) = 1) → A u Φ = Φ)
    (hr : ∀ g ∈ UAt σ Y (evI F), ∀ Φ ∈ P, A g Φ ∈ P)
    (hl : ∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ P, A g Φ ∈ P) (g : UA σ Y.J) : ∀ Φ ∈ P, A g Φ ∈ P := by
  intro Φ hΦ
  have h1 : Tendsto (fun S : Finset (Pl F) => (piece (eps S) (eps_sq S) g)⁻¹ * g) atTop (𝓝 1) := by
    rw [← inv_mul_cancel g]; exact (tendsto_piece g).inv.mul_const g
  obtain ⟨S, h2⟩ := (h1.eventually (hlev Φ hΦ)).exists
  have h4 : ∀ w, (mat ((piece (eps S) (eps_sq S) g)⁻¹ * g)).map (piInf (τ w)) = 1 := fun w => by
    rw [mat_mul, Matrix.map_mul, ← piInf_piece S g, ← Matrix.map_mul, mat_inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨l, l1, l2⟩ := piece_prod g S
  have e : g = piece (eps ∅) (eps_sq ∅) g * l.prod * ((piece (eps S) (eps_sq S) g)⁻¹ * g) := by
    rw [← l2, mul_inv_cancel_left]
  rw [e, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, h2 h4]
  refine hr _ (piece_inf g) _ ?_
  clear e h2 h4 l2
  induction l with
  | nil => simpa using hΦ
  | cons x l ih =>
    obtain ⟨v, hv⟩ := l1 x List.mem_cons_self
    rw [List.prod_cons, map_mul, mul_apply_eq_comp]
    exact hl v x hv _ (ih fun h hh => l1 h (List.mem_cons_of_mem _ hh))

theorem liftAut_k : Tools_k → LiftAut_k := by
  intro T E _ _ _ B n d X W M χX χW om hP hn e e' he he'
  classical
  let C : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ GlobalTheory.UnitaryBC.ratU E n, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp only [Pi.add_apply, ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c _ ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp only [Pi.smul_apply, ha.2 γ hγ g]⟩ }
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl C
  let Pj : (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) :=
    C.subtype ∘ₗ C.projectionOnto C' hC'
  have p1 : ∀ φ, Pj φ ∈ C := fun φ => (C.projectionOnto C' hC' φ).2
  have p2 : ∀ φ ∈ C, Pj φ = φ := fun φ h => congrArg Subtype.val (Submodule.projectionOnto_apply_left hC' ⟨φ, h⟩)
  have fn : ∀ φ ∈ C, IsFn (φ ∘ e.symm) := fun φ h => ⟨h.1.comp e.symm.continuous, fun γ hγ g => by
    show φ (e.symm (γ * g)) = φ (e.symm g); rw [map_mul]; exact h.2 _ ((he.rat _).1 (by simpa using hγ)) _⟩
  have sch : ∀ Φ : PolData B M, Φ.1 ∈ schA (maximalRealSubfield E) (Fin n × Fin d) :=
    fun Φ => PositivityTheory.ThKG.polData_le hP.good Φ.2
  obtain ⟨l1, l2, l3, l4⟩ := lift_lin_pk T hP
  let Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ]
      (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ ψ => lift M om Φ.1 (Pj ψ ∘ e.symm) ∘ e')
      (fun Φ Φ' ψ => funext fun h => congrFun (l1 Φ.1 (sch Φ) Φ'.1 (sch Φ') _ (fn _ (p1 ψ))) (e' h))
      (fun c Φ ψ => funext fun h => congrFun (l2 c Φ.1 (sch Φ) _ (fn _ (p1 ψ))) (e' h))
      (fun Φ ψ ψ' => funext fun h => (by
        show lift M om Φ.1 (Pj (ψ + ψ') ∘ e.symm) (e' h) = _; rw [map_add (f := _)]; rfl :
        _ = _).trans (congrFun (l3 Φ.1 (sch Φ) _ _ (fn _ (p1 ψ)) (fn _ (p1 ψ'))) (e' h)))
      (fun c Φ ψ => funext fun h => (by show lift M om Φ.1 (Pj (c • ψ) ∘ e.symm) (e' h) = _; rw [map_smul]; rfl :
        _ = _).trans (congrFun (l4 c Φ.1 (sch Φ) _ (fn _ (p1 ψ))) (e' h)))
  have q : ∀ (Φ₀ : PolData B M) (φ₀ : GlobalTheory.UnitaryBC.UA E n → ℂ), φ₀ ∈ C →
      Θ Φ₀ φ₀ = lift M om Φ₀.1 (φ₀ ∘ e.symm) ∘ e' := fun Φ₀ φ₀ h => by
    show lift M om Φ₀.1 (Pj φ₀ ∘ e.symm) ∘ e' = _; rw [p2 _ h]
  have hRU : ∀ {Φ} (hΦ : Φ ∈ schA (maximalRealSubfield E) (Fin n × Fin d)) {ψ} (hψ : IsFn ψ)
      (k : GlobalTheory.UnitaryBC.UA E d), RU E d k (lift M om Φ ψ ∘ e') = lift M om (om (1, e' k) Φ) ψ ∘ e' :=
    fun {_} hΦ {_} hψ k => funext fun h => by
      have := lift_equiv_pk T hP hΦ hψ 1 (e' k) (e' h); simp only [mul_one] at this
      exact (congrArg (lift M om _ _) (map_mul e' h k)).trans this.symm
  refine ⟨Θ, fun Φ φ hφ => ?_⟩
  have hφC : φ ∈ C := ⟨hφ.cont, hφ.left⟩
  have hfn := fn φ hφC
  have hs := sch Φ
  refine ⟨q Φ φ hφC, ?_, fun g h => ?_⟩
  · rw [q _ _ hφC]
    refine ⟨(UpperTheory.continuous_thetaLift_of_definite T _ E (cj E) B n d X W M χX χW om hP Φ.1 hs _ hfn).comp
      e'.continuous, fun γ hγ g => ?_, ?_, ?_⟩
    · show lift M om Φ.1 (φ ∘ e.symm) (e' (γ * g)) = lift M om Φ.1 (φ ∘ e.symm) (e' g)
      rw [map_mul]
      refine integral_congr_ae (.of_forall fun g₀ => ?_)
      have h2 := ((T.basic _ E (cj E) B n d X W M χX χW om n 0 d 0 hP).1 Φ.1 hs).2.1 1 (one_mem _) _
        ((he'.rat γ).2 hγ) g₀ (e' g)
      rw [one_mul] at h2; show theta om Φ.1 g₀ (e' γ * e' g) * _ = _; rw [h2]
    · let f := lift M om Φ.1 (φ ∘ e.symm) ∘ e'
      let H : Subgroup (finU (E := E) (n := d)) :=
        { carrier := {k | RU E d k f = f}
          one_mem' := by show RU E d 1 f = f; rw [map_one]; rfl
          mul_mem' := fun ha hb => by
            show RU E d (_ * _) f = f; rw [map_mul, mul_apply_eq_comp, show RU E d _ f = f from hb]; exact ha
          inv_mem' := fun {a} ha => by
            show RU E d a.1⁻¹ f = f; have : RU E d a.1 f = f := ha
            conv_lhs => rw [← this]
            rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl }
      refine Subgroup.isOpen_of_mem_nhds H (g := 1) ?_
      have h1 := PositivityTheory.ThKEnd.Grp.level_sch_k PositivityTheory.ThKEst.level_k hP hs
      have c : Tendsto (fun k : finU (E := E) (n := d) => e' k.1) (𝓝 1) (𝓝 1) :=
        (e'.continuous.comp continuous_subtypeVal).tendsto' _ _ (map_one e')
      filter_upwards [c.eventually h1] with k hk
      show RU E d k.1 f = f
      rw [hRU hs hfn, hk fun w => by
        have h' : ∀ w, (mat (e' k.1)).map (compInf (maximalRealSubfield E) E w) = 1 :=
          Subgroup.closure_induction (k := {g : UA (cj E) W.J |
            (∀ w : InfinitePlace (maximalRealSubfield E), (mat g).map (compInf (maximalRealSubfield E) E w) = 1) ∧
            ∀ v ∈ (∅ : Finset (Pl (maximalRealSubfield E))), OffAt v g})
            (p := fun g _ => ∀ w, (mat g).map (compInf (maximalRealSubfield E) E w) = 1) (fun _ hx => hx.1)
            (fun _ => Matrix.map_one _ (map_zero _) (map_one _))
            (fun x y _ _ hx hy w => by rw [show mat (x * y) = mat x * mat y from rfl, Matrix.map_mul, hx, hy, one_mul])
            (fun x _ hx w => by
              have := congrArg (fun A => A.map (compInf (maximalRealSubfield E) E w))
                (PositivityTheory.ThKEnd.Grp.mat_inv_mul x)
              simpa [Matrix.map_mul, hx w, Matrix.map_one _ (map_zero _) (map_one _)] using this)
            ((he'.fin k.1).2 k.2)
        have e₀ : (mat (e' k.1)).map (piInf (B.emb w)) =
            ((mat (e' k.1)).map (compInf (maximalRealSubfield E) E w)).map (infEmb (B.emb w)) := by ext i j; rfl
        rw [e₀, h', Matrix.map_one _ (map_zero _) (map_one _)]]
    · have hK : ∀ k ∈ gInf (cj E) W, k ∈ KInf (cj E) W B.emb := fun k hk =>
        ⟨Subgroup.closure_induction (p := fun k _ => k ∈ UAt (cj E) W (evI _)) (fun _ hx => hx)
          (fun _ _ => by rw [show mat (1 : UA (cj E) W.J) = 1 from rfl, sub_self, smul_zero])
          (fun g h _ _ hg hh u hu => by
            have e0 : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
              rw [show mat (g * h) = mat g * mat h from rfl, sub_mul, one_mul]; abel
            rw [e0, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero])
          (fun g _ hg u hu => by
            have e0 : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
              rw [mul_sub, show mat g⁻¹ * mat g = 1 from PositivityTheory.ThKEnd.Grp.mat_inv_mul g, mul_one, neg_sub]
            rw [e0, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]) hk,
         fun w => by rw [Prs.cartan_one (hP.skew.sig w) (hP.skew.cartan w)]; exact Commute.one_right _⟩
      have hfd_gen : ∀ Ψ ∈ PolData B M, ∃ V : Submodule ℂ (Fn (maximalRealSubfield E) n d),
          FiniteDimensional ℂ V ∧ V ≤ schA (maximalRealSubfield E) (Fin n × Fin d) ∧
          ∀ k ∈ gInf (cj E) W, om (1, k) Ψ ∈ V := fun Ψ hΨ => by
        induction hΨ using Submodule.span_induction with
        | mem _ hx =>
          obtain ⟨f, hf, φ₀, h1, h2, rfl⟩ := hx
          have hfin : {v | ¬ φ₀ v = M.vac v}.Finite := h2
          have hD : Prs.Dat B M hfin.toFinset f φ₀ := ⟨hf, h1, fun _ hv => by simpa using hv⟩
          obtain ⟨g₀, hg₀, e₀⟩ := hD.pureA hP.good
          obtain ⟨U, hU, hU'⟩ := polFin_k hP f hf
          let pL : SInf (maximalRealSubfield E) (Fin n × Fin d) →ₗ[ℂ] Fn (maximalRealSubfield E) n d :=
            { toFun := fun f' => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ₀
              map_add' := fun _ _ => funext fun _ => by
                simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
              map_smul' := fun c _ => funext fun _ => by
                simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc] }
          refine ⟨U.map pL, inferInstance, by rintro _ ⟨f', -, rfl⟩; exact Submodule.subset_span ⟨f', g₀, hg₀, e₀ f'⟩,
            fun k hk => ?_⟩
          obtain ⟨A, hA⟩ := Prs.inf_op_k PositivityTheory.ThKF.A.archOp_k hP (hK k hk)
          have hact := (hA f hf).2
          exact ⟨A f, hU' k (hK k hk) _ hact, (hact _ (hD.rest hP.good)).symm⟩
        | zero => exact ⟨⊥, inferInstance, bot_le, fun _ _ => by simp⟩
        | add _ _ _ _ hx hy =>
          obtain ⟨V, _, h2, h3⟩ := hx; obtain ⟨V', _, h2', h3'⟩ := hy
          exact ⟨V ⊔ V', inferInstance, sup_le h2 h2', fun k hk => by
            rw [map_add (f := _)]; exact Submodule.add_mem_sup (h3 k hk) (h3' k hk)⟩
        | smul c _ _ hx =>
          obtain ⟨V, _, h2, h3⟩ := hx
          exact ⟨V, inferInstance, h2, fun k hk => by rw [map_smul]; exact V.smul_mem c (h3 k hk)⟩
      obtain ⟨V, hV, hVs, hk⟩ := hfd_gen Φ.1 Φ.2
      let L : V →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
        { toFun := fun x => lift M om x.1 (φ ∘ e.symm) ∘ e'
          map_add' := fun x y => funext fun h => congrFun (l1 x.1 (hVs x.2) y.1 (hVs y.2) _ hfn) (e' h)
          map_smul' := fun c x => funext fun h => congrFun (l2 c x.1 (hVs x.2) _ hfn) (e' h) }
      refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨⟨_, hk _ ((he'.inf k.1).2 k.2)⟩, (hRU hs hfn k.1).symm⟩
  · have hlevS : ∀ Ψ ∈ schA (maximalRealSubfield E) (Fin n × Fin d), ∀ᶠ u in 𝓝 (1 : UA (cj E) X.J),
        (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (u, 1) Ψ = Ψ := fun Ψ hΨ => by
      induction hΨ using Submodule.span_induction with
      | mem _ hm =>
        obtain ⟨f, g₀, hg₀, rfl⟩ := hm
        obtain ⟨U, hU, hU'⟩ := levelX_pure_pk hP hg₀
        exact mem_of_superset hU fun u hu k => hU' u hu k f
      | zero => exact Eventually.of_forall fun _ _ => map_zero _
      | add _ _ _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add (f := _), h1 k, h2 k]
      | smul _ _ _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]
    have hlevX : ∀ Ψ ∈ PolData B M, ∀ᶠ u in 𝓝 (1 : UA (cj E) X.J),
        (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (u, 1) Ψ = Ψ :=
      fun Ψ hΨ => hlevS Ψ (PositivityTheory.ThKG.polData_le hP.good hΨ)
    have o1 : ∀ {m : ℕ} {v : Pl (maximalRealSubfield E)} (Y : Spc (maximalRealSubfield E) E m),
        (1 : UA (cj E) Y.J) ∈ UAt (cj E) Y (evFin _ v) := fun Y => PositivityTheory.ThKH.Locrep.one_mem_UAt Y _
    have o2 : ∀ {m : ℕ} (Y : Spc (maximalRealSubfield E) E m), (1 : UA (cj E) Y.J) ∈ UAt (cj E) Y (evI _) :=
      fun Y _ _ => by rw [show mat (1 : UA (cj E) Y.J) = 1 from rfl, sub_self, smul_zero]
    have hm : om (e g, e' h) Φ.1 ∈ PolData B M := by
      rw [show ((e g, e' h) : UA (cj E) X.J × UA (cj E) W.J) = (e g, 1) * (1, e' h) by simp, map_mul, mul_apply_eq_comp]
      refine stab_of_pk B.emb (om.comp (MonoidHom.inl _ _)) _ hlevX
        (fun _ hg _ h' => pol_arch_pk hP hg (o2 W) h') (fun v _ hg _ h' => pol_fin_pk T hP v hg (o1 W) h') (e g) _ ?_
      exact stab_of_pk B.emb (om.comp (MonoidHom.inr _ _)) _
        (fun _ h' => PositivityTheory.ThKEnd.Grp.level_sch_k PositivityTheory.ThKEst.level_k hP
          (PositivityTheory.ThKG.polData_le hP.good h'))
        (fun _ hg _ h' => pol_arch_pk hP (o2 X) hg h') (fun v _ hg _ h' => pol_fin_pk T hP v (o1 X) hg h') (e' h) _ Φ.2
    refine ⟨⟨_, hm⟩, rfl, ?_⟩
    have hRC : RU E n g φ ∈ C := ⟨hφ.cont.comp (continuous_mul_const g), fun γ hγ x => by
      show φ (γ * x * g) = φ (x * g); rw [mul_assoc]; exact hφ.left γ hγ _⟩
    rw [q _ _ hRC, q _ _ hφC]
    funext h₀
    have h1 := lift_equiv_pk T hP hs hfn (e g) (e' h) (e' h₀)
    have e1 : RU E n g φ ∘ e.symm = fun y => (φ ∘ e.symm) (y * e g) := funext fun y => by
      show φ (e.symm y * g) = φ (e.symm (y * e g)); rw [map_mul, e.symm_apply_apply]
    rw [e1]; exact h1.trans (congrArg (lift M om Φ.1 (φ ∘ e.symm)) (map_mul e' h₀ h).symm)

end UpperTheory.TP
end
end
