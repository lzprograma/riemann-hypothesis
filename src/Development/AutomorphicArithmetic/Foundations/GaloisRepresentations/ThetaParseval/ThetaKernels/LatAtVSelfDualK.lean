module

public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AdelicSchrodingerTensorEqLocalOfSupportedAt
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseEisCont
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
public import Development.WeilBound.CoreStatements.LocalThetaKernels.ExistsSmallSubgroups
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
public import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.StarMemSchA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenAlg
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepAd
public import Development.WeilBound.ThetaLifts.LatticeBasics.SchrUnit
public import Development.WeilBound.ThetaLifts.LatticeBasics.SkewTwo
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PresOfHat
public import GroundTheory.LocalFields.LocalFourierHaar

/-! # LatAtVSelfDualK: Consolidated global theta-kernel definitions and proofs (LatAtVSelfDualK). -/
@[expose] public section

open UpperTheory.TP.W (GoodK)

noncomputable section
open UpperTheory.TP.W (GoodK)
namespace PositivityTheory.ThK
open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
structure PairOK_k (B : Base F E) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) : Prop where
  base : GoodK σ B
  herm : ∃ r s, X.IsHerm σ B r s
  skew : ∃ r s, W.IsSkew σ B r s
  good : M.IsGood B.ψ
  weil : ∃ χX χW, M.IsWeil B.ψ χX χW om
def AllPairs_k (Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n
  d : ℕ}
    (_ : Base F E) {X : Spc F E n} {W : Spc F E d} (_ : Model σ X W) (_ : Rep σ X W), Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F
    E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W), PairOK_k B X W M om → ∀ v, Q B M om v
def LocRepEx_k : Prop := AllPairs_k fun B _ _ M om v => ∃ ω ρ, IsLocRep M B.ψ om v ω ρ
def InertOf_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∃ w, Formalism.UG.IsInertAt F E v w
end PositivityTheory.ThK

namespace PositivityTheory.ThK
open NumberField IsDedekindDomain GlobalTheory.AdelicU
theorem inertof_proof_k : InertOf_k := by
  intro F E _ _ _ _ _ σ B hB v he
  have := hB.unram
  have := v.isMaximal
  have h1 := ncard_primesOver_le_two hB.cm v
  have h2 : (v.asIdeal.primesOver (𝓞 E)).ncard ≠ 2 := fun h =>
    not_nonempty_iff.2 he ((nonempty_split_iff hB.cm).2 h)
  have h3 : 0 < (v.asIdeal.primesOver (𝓞 E)).ncard := Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)
  exact map_eq_of_ncard_eq_one v (by omega)
end PositivityTheory.ThK
end

section
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField MeasureTheory Matrix Classical GlobalTheory.FunObj GlobalTheory.ChiGrid
  GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open UpperTheory.TP.W (GoodK)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
noncomputable section
namespace GlobalTheory.LatVacArith
section Final
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem psi_symp_latAtV_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n d : ℕ} (X :
      Spc F E n)
    (Y : Spc F E d) (r s r' s' : ℕ),
    GoodK σ B → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (v :
      Pl (F := F)) (θ : 𝓞 E) (b : AF F),
    GlobalTheory.AdelicU.evFin F v b ∈ v.adicCompletionIntegers F →
    ∀ γ ∈ latAtV X Y v,
      ∀ γ' ∈ latAtV X Y v,
      B.ψ (b * GlobalTheory.WeilM.symp (R := AF F) (cA σ)
        (inclR (F := F) (AF F) (θ : E))
        (incM F X.J)
          (incM F Y.J) γ γ') = 1 :=
  Tw.LatVacArith.psi_symp_latAtV_k
end Final
end GlobalTheory.LatVacArith
end
end

section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Idele WithZero
open UpperTheory.TP.W (GoodK)
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)
noncomputable section
namespace GlobalTheory.LatSelfDualAll
open GlobalTheory.InertSelfDual (exists_traceFamily det_ne_zero_of_herm det_ne_zero_of_skew decomp hTens_frame
  trace_expand)
theorem latAtV_selfDual_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
      GoodK σ B →
    X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) z →
      (z ∈ latAtV X W v ↔ ∀ γ ∈ latAtV X W v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B n d X W r₁ s₁ r₂ s₂ hB hX hW v z hz
  constructor
  · intro hzm γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV_k σ B X W _ _ _ _ hB hX hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    have := hB.unram
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, -, hTS⟩ := exists_formFrame' σ X.J (det_ne_zero_of_herm σ B hX) X.L hX.lat
      (fun y hy => (hX.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTd', hTS'⟩ := exists_formFrame' σ W.J (det_ne_zero_of_skew σ B hW) W.L
      (by first | exact hW.lat | exact hW.lat.toIsLattice)
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (X.J * S.map σ)ᵀ * z * (incM F (W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (X.J * S.map σ)ᵀ * (u • z) * (incM F (W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, ∀ y ∈ v.adicCompletionIntegers F,
        psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l)) * y) = 1 := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ X.L := by
        have := X.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV X W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y,
            by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y)
          z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [Tw.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      intro y hy
      have := key (-y) (neg_mem hy)
      rwa [htC, map_neg, neg_mul_neg] at this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (c i : E) * C j l)) * y) = 1 := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (X.J * S.map σ)ᵀ T' (W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have hxi : (fun r => (s i : E) * T r j) ∈ X.L := by
      have := X.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    have hat : At (evFin F v) (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (c i : E) * C j l)) := by
      intro u hu
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    have hmem := smul_mem_latAtV σ B hB.std hX hW v hat (hint' i j l) hxi (hTm' l) (hTd' l)
    convert hmem using 1
    rw [smul_assoc]
    congr 1
    ext p q
    simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
    ring
end GlobalTheory.LatSelfDualAll
end
end

noncomputable section
namespace PositivityTheory.ThK.Vac
open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.LatVac
open GlobalTheory.StdDual (codiff codiff_ne_zero)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem mem_latW_k {B : Base F E} (hB : GoodK σ B) {W : Spc F E d} {r s : ℕ} (hW : W.IsSkew σ B
  r s) (v : Pl F)
    {w : Fin d → AE F E} (hw : At (evFin F v) w)
    (h : ∀ y ∈ W.L, ∀ a ∈ v.adicCompletionIntegers F, B.ψ (liftV v a * trF σ W.J y w) = 1) : w ∈ latW W v := by
  have hσ := sigma_sigma hB.cm
  have hfull : Submodule.span E (W.L : Set (Fin d → E)) = ⊤ := by
    let T := Submodule.span E (W.L : Set (Fin d → E))
    change T = ⊤
    by_contra hT
    let g : (Fin d → E) →ₗ[E] Module.Dual E T :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin W.Jᵀ)).domRestrict₂ T
    have hdim : Module.finrank E (Module.Dual E T) < Module.finrank E (Fin d → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hT
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin d → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin d → E) (hx : x ∈ W.L) : form σ W.J y x = 0 := by
      have hz' : z ⬝ᵥ W.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E T => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      rw [Matrix.dotProduct_transpose_mulVec] at hz'
      have hz'' : form σ W.J x y = 0 := by
        simpa only [form, y, sigma_sigma hB.cm] using hz'
      have hs : σ (form σ W.J y x) = (-1 : E) * form σ W.J x y := by

        simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hW.skew, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hz'', mul_zero] at hs
      exact (map_eq_zero σ).1 hs
    have hline (a : E) : a • y ∈ W.L := (hW.dual _).2 fun x hx => by
      have he : form σ W.J (a • y) x = 0 := by
        change (a • y) ⬝ᵥ W.J *ᵥ (fun i => σ (x i)) = 0
        rw [smul_dotProduct, smul_eq_mul, show y ⬝ᵥ W.J *ᵥ (fun i => σ (x i)) = 0 from horth x hx, mul_zero]
      simp only [he, mul_zero, map_zero]
      exact fun _ => isIntegral_zero
    let i : E →ₗ[𝓞 E] W.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict W.L hline
    let : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 F) F (W.L.restrictScalars (𝓞 F)) (hW.lat.fg.restrictScalars) (by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E
      (W.L : Set (Fin d → E)) x (hfull ▸ Submodule.mem_top)
    obtain ⟨_, k, hk, rfl⟩ := t
    rw [Submodule.span_eq] at ht
    have hk0 : (k : F) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)
    have ht' : (k : F) • x ∈ W.L := by
      rw [Int.cast_smul_eq_zsmul, ← algebraMap_smul (𝓞 E) k x]; exact ht
    rw [← inv_smul_smul₀ hk0 x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ht'))
  choose u hu using fun i => exists_tr_rep hσ (skew_det hW) (f i)
  have hdec : ∀ z : Fin d → AE F E, z = ∑ i, trF σ W.J (u i) z • incV (g i) := fun z => by
    have hz := span_incV z
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      simp only [trF_incV, ← hu]
      ext j
      conv_lhs => rw [hid x]

      simp only [incV, Finset.sum_apply, Pi.smul_apply, map_sum, algebraMap_smul]
      exact Finset.sum_congr rfl fun i _ =>
        map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, ← hx, ← hy]
    | smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]
  rw [hdec w]
  refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, fun a ha => ?_, ?_, g i, hg i, rfl⟩
  · rw [← map_smul, hw a ha, map_zero]
  · refine mem_int_of_psi hB.std v _ fun t ht a ha => ?_
    have hm : algebraMap F E t • u i ∈ W.L := (hW.dual _).2 fun x hx o => by
      let o' : 𝓞 E := ⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩
      obtain ⟨c, hc⟩ := hf i _ (W.L.smul_mem o' hx)
      have e : (o : E) * form σ W.J (algebraMap F E t • u i) x = t • form σ W.J (u i) (o' • x) := by
        rw [form_eq, form_eq, Algebra.smul_def t, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : (o' • x) l = σ o * x l := rfl
        rw [this, map_mul, hσ, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, ← Algebra.trace_trace (S := F), map_smul, ← hu, ← hc, smul_eq_mul]
      obtain ⟨k, hk⟩ := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).1 ht _
        ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
      rw [Algebra.traceForm_apply] at hk
      rw [← hk]
      exact isIntegral_algebraMap
    have := h _ hm a ha
    rwa [trF_smul, liftV_mul, map_mul (evFin F v), AlgHom.commutes] at this
theorem mem_latAtV_k {B : Base F E} (hB : GoodK σ B) {X : Spc F E n} {W : Spc F E d} {r s r' s'
  : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (v : Pl F) {z : Matrix (Fin n) (Fin d) (AE F E)} (hz : At (evFin F v) z)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ z) = 1) : z ∈ latAtV X W v :=
      by
  have hσ := sigma_sigma hB.cm
  have hfull : Submodule.span E (X.L : Set (Fin n → E)) = ⊤ := by
    let T := Submodule.span E (X.L : Set (Fin n → E))
    change T = ⊤
    by_contra hT
    let g : (Fin n → E) →ₗ[E] Module.Dual E T :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin X.Jᵀ)).domRestrict₂ T
    have hdim : Module.finrank E (Module.Dual E T) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hT
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin n → E) (hx : x ∈ X.L) : form σ X.J y x = 0 := by
      have hz' : z ⬝ᵥ X.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E T => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      rw [Matrix.dotProduct_transpose_mulVec] at hz'
      have hz'' : form σ X.J x y = 0 := by
        simpa only [form, y, sigma_sigma hB.cm] using hz'
      have hs : σ (form σ X.J y x) = (1 : E) * form σ X.J x y := by

        simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hX.herm, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hz'', mul_zero] at hs
      exact (map_eq_zero σ).1 hs
    have hline (a : E) : a • y ∈ X.L := (hX.dual _).2 fun x hx => by
      have he : form σ X.J (a • y) x = 0 := by
        change (a • y) ⬝ᵥ X.J *ᵥ (fun i => σ (x i)) = 0
        rw [smul_dotProduct, smul_eq_mul, show y ⬝ᵥ X.J *ᵥ (fun i => σ (x i)) = 0 from horth x hx, mul_zero]
      rw [he]
      exact isIntegral_zero
    let i : E →ₗ[𝓞 E] X.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict X.L hline
    let := Module.Finite.iff_fg.mpr hX.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 E) E X.L hX.lat.fg hfull
  let a : Fin m → Fin n → E := fun i k => f i (Pi.single k 1)
  let u : Fin m → Fin n → E := fun i => (fun k => σ (a i k)) ᵥ* X.J⁻¹
  have hu : ∀ i, u i ᵥ* X.J = fun k => σ (a i k) := fun i => by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (herm_det hX), Matrix.vecMul_one]
  have huL : ∀ i, u i ∈ X.L := fun i => (hX.dual _).2 fun x hx => by
    obtain ⟨c, hc⟩ := hf i x hx
    have e : form σ X.J (u i) x = σ (f i x) := by

      rw [form_eq, hu, LinearMap.pi_apply_eq_sum_univ (f i) x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [this]
    rw [e, ← hc]
    exact (RingOfIntegers.isIntegral_coe c).map (σ.restrictScalars ℤ)
  have hdec : z = ∑ i, Matrix.vecMulVec (incV (g i)) (incV (a i) ᵥ* z) := by
    ext p l
    have e : ∀ k, ∑ i, incV (g i) p * incV (a i) k = (1 : Matrix (Fin n) (Fin n) (AE F E)) p k := fun k => by
      have := congrFun (hid (Pi.single k 1)) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this

      simp only [incV, ← map_mul, ← map_sum, mul_comm (g _ p), a, ← this, Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, e]
    exact (congrFun (congrFun (Matrix.one_mul z) p) l).symm
  rw [hdec]
  refine sum_mem fun i _ => vecMulVec_mem (hg i) (mem_latW_k hB hW v (fun c hc =>
    ?_) fun y hy c hc => ?_)
  · rw [← Matrix.vecMul_smul, hz c hc, Matrix.vecMul_zero]
  · have := h _ (neg_mem (AddSubgroup.subset_closure ⟨liftV v c, at_liftV v c, by rwa [evFin_liftV], u i, huL i, y, hy,
      rfl⟩))
    rw [GlobalTheory.LatVacArith.symp_neg_left, ← one_smul (AF F) z, symp_smul_smul, symp_vecMulVec hσ, hu] at this
    simpa only [hσ, mul_one, mul_neg, neg_neg] using this
end PositivityTheory.ThK.Vac
end

noncomputable section
namespace PositivityTheory.ThKH.Locrep
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem locRepEx_k : PositivityTheory.ThK.LocRepEx_k := by
  intro F E _ _ _ _ _ σ n d B X W M om hP v
  obtain ⟨χX, χW, hw⟩ := hP.weil
  have hs := IsUWeilPair.isUSplitting hw
  have hstd := hP.base.std
  have hne : B.ψ ≠ 1 := fun h => Tw.PsiNontriv.psiV_ne_one B.ψ hstd v (by rw [h]; rfl)
  have hH := (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F (Fin n × Fin d) B.ψ hstd.1 hne hstd.2.1).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ) → Module.End ℂ (Fn F n d v) := fun T =>
    res v x₀ ∘ₗ T ∘ₗ tensL v r₀
  have hloc : ∀ T φ, loc T φ = res v x₀ (T (tens (evFin F v) φ r₀)) := fun _ _ => rfl
  have pres : ∀ p, ∀ φ ∈ SB _, loc (om p) φ ∈ SB _ := fun p φ hφ => res_mem v x₀ (hs.pres p _ (h₀ φ hφ).2)
  have presH : ∀ u, ∀ φ ∈ SB _, loc (schrL B.ψ (M.co.e u)) φ ∈ SB _ := fun u φ hφ => res_mem v x₀ (hH _ _ (h₀ φ hφ).2)
  have acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      Acts (evFin F v) (om (g, h)) φ (loc (om (g, h)) φ) := by
    intro g hg h hh φ hφ
    refine acts_res v hstd.1 hne hstd.2.1 (hs.pres _) (hs.adm _) (fun w h1 h2 Φ hΦ => ?_) h₁ hφ (h₀ φ hφ)
    obtain ⟨u, rfl⟩ := M.co.e.surjective w
    have hu : atPlace v (1 : Fv F v) • u = 0 := by
      apply M.co.e.injective
      rw [map_smul, map_zero]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · change atPlace v 1 * (M.co.e u).1 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).1 i) = 0 from congrFun h1 i, mul_zero, map_zero]
      · change atPlace v 1 * (M.co.e u).2 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).2 i) = 0 from congrFun h2 i, mul_zero, map_zero]
    have := hs.impl (g, h) u Φ hΦ
    rwa [show actAB (cA σ) (g, h) u = u from act_away hg hh hu] at this
  have actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
      Acts (evFin F v) (M.co.rho B.ψ u) φ (loc (schrL B.ψ (M.co.e u)) φ) := by
    intro u hu φ hφ
    have e : ∀ a, evFin F v a = 0 → a • M.co.e u = 0 := fun a ha => by rw [← map_smul, hu a ha, map_zero]
    have A : Acts (evFin F v) (M.co.rho B.ψ u) φ _ := fun r hr =>
      Tw.SchrLoc.schr_tens_of_at B.ψ v (M.co.e u) (fun i a ha => congrFun (congrArg Prod.fst (e a ha)) i)
        (fun i a ha => congrFun (congrArg Prod.snd (e a ha)) i) φ r hr.1
    have := eq_of_acts v h₁ (h₀ φ hφ) A
    rw [this] at A
    exact A
  have one : ∀ φ ∈ SB _, loc (om 1) φ = φ := fun φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm
  have mul : ∀ p : UA σ X.J × UA σ W.J, ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      loc (om (p * (g', h'))) φ = loc (om p) (loc (om (g', h')) φ) := fun p g' hg' h' hh' φ hφ => by
    rw [hloc, hloc (om p), ← acts g' hg' h' hh' φ hφ r₀ (h₀ φ hφ), map_mul]
    rfl
  refine ⟨fun p => loc (om p), fun u => loc (schrL B.ψ (M.co.e u)), fun g _ h _ => pres _,
    fun g hg h hh φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ acts g hg h hh φ hφ⟩, one,
    fun g _ h _ => mul (g, h), fun φ hφ => ?_, fun u _ => presH u,
    fun u hu φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ actsH u hu φ hφ⟩,
    fun g hg h hh u hu φ hφ => ?_⟩
  · obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ W v
    obtain ⟨m, hm⟩ := smooth_of_weak (SB _) K hK1 hK2 (fun h => loc (om (1, h))) (fun h _ => pres _) one
      (fun h _ h' hh' φ hφ => by
        have := mul (1, h) 1 (one_mem_UAt X v) h' (hK3 0 hh') φ hφ
        rwa [Prod.mk_mul_mk, one_mul] at this)
      (fun l φ hφ => (hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2).comp (continuous_const.prodMk continuous_id)) φ hφ
    obtain ⟨U, hU, hUK⟩ := hK4 m
    exact ⟨U, hU, fun h hh hv => hm h (hUK h hh hv)⟩
  · change loc (om (g, h)) (loc (schrL B.ψ (M.co.e u)) φ) = loc (schrL B.ψ (M.co.e _)) (loc (om (g, h)) φ)
    rw [hloc (om (g, h)), hloc _ (loc (om (g, h)) φ), ← actsH u hu φ hφ r₀ (h₀ φ hφ),
      ← acts g hg h hh φ hφ r₀ (h₀ φ hφ), hs.impl _ _ _ (h₀ φ hφ).2]
    rfl
end PositivityTheory.ThKH.Locrep
end

noncomputable section
open UpperTheory.TP.W (GoodK)
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def VacFix2_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s',
    GoodK σ B → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ → ∀ χ : Chr F E, IsHecke F E χ → ∀ dd om, IsDblCoordX M dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χ (diagCols (Fin n)) om →
    ∀ K, IsStab2 (Y := X) B K → ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
      Acts (evFin F v) (om k) (boxFun (M.vac v) (star (M.vac v))) (boxFun (M.vac v) (star (M.vac v)))
end GlobalTheory.ThK.Dbl

namespace PositivityTheory.ThKG.Loc.Cone.Vf
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v :
  Pl F}
theorem dbl_eigen_k {B : Base F E} (hB : GoodK σ B) {X : Spc F E n} {W : Spc F E d} {r s r' s' :
  ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} {φ} (hφ : M.IsVac B.ψ v φ)
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)} (hd' : ∀ x,
      d'.e xᵀ = M.co.e x)
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))}
    (hdd : IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd) {omd}
    (hsp : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd) (g : UG (cA σ) (dbl (incM F X.J)))
    (hg : At (evFin F v) (g.1.1 - 1)) (hg' : PresD v X (g⁻¹).1.1) :
    ∃ c : ℂ, Acts (evFin F v) (omd g) (boxFun φ (star φ)) (c • boxFun φ (star φ)) := by
  obtain ⟨hs, h0, θ, -, hθ⟩ := hφ
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have hv : ∀ γ ∈ latAtV X W v, schr (psiAt B.ψ v) (locCo M.co v γ) φ = _ := fun γ hγ =>
    (eq_of_acts v h₁ (h₀ φ hs) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) φ)).trans
      (eq_of_acts v h₁ (h₀ φ hs) (hθ γ hγ)).symm
  set θ' := inclR (F := F) (AF F) (θ : E)
  refine eigen dd hB.std {z | ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, z = Matrix.fromCols γ₁ᵀ γ₂ᵀ} ?_ ?_
    (fun z => B.ψ (⅟(2 : AF F) * symp (cA σ) θ' (incM F W.J) (dbl (incM F X.J)) z z)) (sb_box_loc hs (sb_star hs)) ?_ ?_
    (omd g) (hsp.pres g) (hsp.adm g) (actB (cA σ) g) (hsp.impl g) ?_ ?_
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩ u hu
    ext i (j | j)
    exacts [congrFun (congrFun (hAt _ h1 u hu) j) i, congrFun (congrFun (hAt _ h2 u hu) j) i]
  · intro z hz h
    have ez : z = Matrix.fromCols (z.toCols₁ᵀ)ᵀ (z.toCols₂ᵀ)ᵀ := (Matrix.fromCols_toCols z).symm
    refine ⟨_, PositivityTheory.ThK.Vac.mem_latAtV_k hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, _,
      PositivityTheory.ThK.Vac.mem_latAtV_k hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, ez⟩
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inl i)
    · have := h _ ⟨γ, hγ, 0, zero_mem _, rfl⟩
      rwa [ez, symp_dbl, symp_zero, sub_zero] at this
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inr i)
    · have := h _ ⟨0, zero_mem _, -γ, neg_mem hγ, rfl⟩
      rwa [ez, symp_dbl, symp_zero, zero_sub, ← neg_one_smul (AF F) γ, symp_smul, neg_one_mul, neg_neg] at this
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    exact fun e => mul_ne_zero hx (star_ne_zero.2 hx) (congrFun e (Sum.elim x x))
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    have e : locCo dd v (Matrix.fromCols γ₁ᵀ γ₂ᵀ) = (Sum.elim (locCo M.co v γ₁).1 (locCo M.co v γ₂).1,
        Sum.elim (locCo M.co v γ₁).2 (-(locCo M.co v γ₂).2)) := by
      have := hdd γ₁ᵀ γ₂ᵀ
      rw [hd', hd'] at this
      ext (i | i) <;> simp [locCo, this]
    have a2 : At (evFin F v) (⅟(2 : AF F) * symp (cA σ) θ' (incM F X.J) (incM F W.J) γ₂ γ₂) := fun u hu => by
      rw [smul_eq_mul, mul_left_comm, ← symp_smul, hAt _ h2 u hu, symp_zero, mul_zero]
    rw [e, schr_box hB.std, hv _ h1, hv _ h2, symp_dbl, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul,
      ← star_psi hB.std a2]
    funext x
    simp only [boxFun, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  · intro u hu
    have : u * (g.1.1 - 1)ᵀ = 0 := by
      rw [← idem_smul hg, Matrix.transpose_smul, Matrix.mul_smul, ← Matrix.smul_mul]
      change (sg v 1 • u) * _ = 0
      rw [hu, Matrix.zero_mul]
    rwa [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    obtain ⟨a, ha, b, hb, c, hc, e, he, eg⟩ := hg'
    refine ⟨Matrix.fromCols γ₁ᵀ γ₂ᵀ * ((g⁻¹).1.1)ᵀ, ⟨a * γ₁ + b * γ₂, add_mem (mul_latAtV ha h1) (mul_latAtV hb h2),
      c * γ₁ + e * γ₂, add_mem (mul_latAtV hc h1) (mul_latAtV he h2), ?_⟩, ?_, ?_⟩
    · rw [eg, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_add, Matrix.transpose_mul]
    · have : g.1.1 * (g⁻¹).1.1 = 1 := g.1.mul_inv
      rw [actB, Matrix.mul_assoc, ← Matrix.transpose_mul, this, Matrix.transpose_one, Matrix.mul_one]
    · rw [symp, symp, hTens_mul (cA σ) _ (g⁻¹).2]
end PositivityTheory.ThKG.Loc.Cone.Vf

namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep
  PositivityTheory.ThKG.Loc.Cone.Vf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v :
  Pl F}
theorem _root_.GlobalTheory.ThK.Dbl.vacFix2_k : VacFix2_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM χ _ dd omd ⟨d', hd', hdd⟩ ⟨_, hsp, hrule⟩ K hK v hv g hk hg
  have hL := hX.lat
  have vd := hM.vac v
  obtain ⟨hsb, h0, -⟩ := hM.vac v
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y₀) = M.vac v y₀ := by
    change M.vac v (evA _ v (putA v x₀ y₀)) * r₀ (putA v x₀ y₀) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have q1 : PresD v X g.1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g (.inl rfl)
  have q2 : PresD v X (g⁻¹).1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g⁻¹ (.inr rfl)
  obtain ⟨c, hc⟩ := PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g hg q2
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨g₁, m₁, g₂, m₂, g₃, m₃, g₄, m₄, eg⟩ := q1
  obtain ⟨a₁, n₁, a₂, n₂, a₃, -, a₄, -, ea⟩ := q2
  have hD : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows (g₁ + g₂) (g₃ + g₄) := by
    rw [eg, diagCols, Matrix.fromBlocks_mul_fromRows]; simp
  have hI : a₁ * (g₁ + g₂) + a₂ * (g₃ + g₄) = 1 := by
    have : (g⁻¹).1.1 * (g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E))) = diagCols (Fin n) := by
      rw [← Matrix.mul_assoc, show (g⁻¹).1.1 * g.1.1 = 1 from g.1.inv_mul, Matrix.one_mul]
    rw [hD, ea, Matrix.fromBlocks_mul_fromRows, diagCols] at this
    exact (Matrix.fromRows_inj this).1
  have aD := at_mul_left (M := g.1.1 - 1) hg (diagCols (Fin n) : Matrix _ _ (AE F E))
  rw [Matrix.sub_mul, Matrix.one_mul, hD] at aD
  have ax : At (evFin F v) (g₁ + g₂ - 1) := fun u hu => congrArg Matrix.toRows₁ (aD u hu)
  have ay : At (evFin F v) (g₃ + g₄ - 1) := fun u hu => congrArg Matrix.toRows₂ (aD u hu)
  have px := add_mem m₁ m₂
  have py := add_mem m₃ m₄
  generalize g₁ + g₂ = x at *
  generalize g₃ + g₄ = y at *
  obtain ⟨b, b', t', b1, hb, pb, pt, ht⟩ := exists_beta_k hB hX g hD px py n₁ n₂ hI ax ay
  have hm : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  have pm := sub_mem py px
  let εv : AE F E := eps v
  obtain ⟨s₀, n₀, p, t, ss, eg', es, en, en', hn, hp, et, et'⟩ :=
    Vf2.exists_decomp b1 hb g hD ht (ε := εv) eps_mul ((cA σ).commutes _) (eps_smul hm)
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v εv = 1 := by
    rw [show εv = PositivityTheory.ThKG.Loc.Cone.Vf.eps v from rfl, PositivityTheory.ThKG.Loc.Cone.Vf.eps, comp_alg,
      ev_sg]; rfl
  have pe : εv • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - εv) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have hd0 : boxFun Φ (star Φ) ≠ 0 := fun e => lDiag_ne hΦs hΦ0 (by rw [e, map_zero])
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • εv = 0 := at_eps u hu
      rw [SS, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add,
        Matrix.fromBlocks_smul]
      simp only [sub_smul, one_smul, neg_zero, add_zero, ← sub_eq_add_neg, sub_sub_cancel_left, smul_neg, ← smul_assoc,
        this, zero_smul, Matrix.fromBlocks_zero])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [at_mul_left hm t' u hu, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pm pt, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, mul_apply_eq_comp, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, one_apply_eq_self] at e
    exact smul_left_injective ℂ hd0 (e.symm.trans (one_smul _ _).symm)
  have e1 : omd g (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by rw [bt, hc _ rd, tens_smul]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, ha, map_smul, ha', a1, one_smul, map_smul, ha,
        smul_smul, aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * g := by rw [eg', inv_mul_cancel_left]
    rw [this, map_mul, mul_apply_eq_comp, e1, map_smul]
    conv_lhs => rw [← e3, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χ hv t (by rw [et]; exact add_mem py (mul_mem pb pm))
    (by rw [et']; exact pt)
    (by rw [et, add_sub_right_comm]; exact at_add ay (at_mul_right _ hm))) hΦs hΦ0 e2
  have n4 := Bad.norm_eig hsp.unit hsp.pres hΦd hd0 e1
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]
end GlobalTheory.ThK.Dbl.Vf2
end

noncomputable section
namespace PositivityTheory.ThKF0
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK PositivityTheory.ThKH.Locrep
theorem actsEx_k : GlobalTheory.ThK.ActsEx_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  obtain ⟨ω, ρ, L⟩ := PositivityTheory.ThKH.Locrep.locRepEx_k F E σ n d B X W M om ⟨hP.base, ⟨r, s, hP.herm⟩,
    ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v) := fun p => res v x₀ ∘ₗ om p ∘ₗ tensL v r₀
  have hloc : ∀ p : UA σ X.J × UA σ W.J, p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _,
      loc p φ = ω p φ := fun p h1 h2 φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) ((L.acts p.1 h1 p.2 h2 φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
  obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
  obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
    (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
    (fun U hU => by
      obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨a, ha⟩ := hK2 U₁ h1
      obtain ⟨b, hb⟩ := hK2' U₂ h2
      exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
    loc (fun p hp φ hφ => by
      rw [hloc p (hK3 0 hp.1) (hK3' 0 hp.2) φ hφ]
      exact L.pres p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) φ hφ)
    (fun φ hφ => by
      rw [hloc 1 (one_mem_UAt X v) (one_mem_UAt W v) φ hφ]
      exact L.one φ hφ)
    (fun p hp q hq φ hφ => by
      rw [hloc (p * q) (mul_mem_UAt (hK3 0 hp.1) (hK3 0 hq.1)) (mul_mem_UAt (hK3' 0 hp.2) (hK3' 0 hq.2)) φ hφ,
        hloc q (hK3 0 hq.1) (hK3' 0 hq.2) φ hφ,
        hloc p (hK3 0 hp.1) (hK3' 0 hp.2) _ (L.pres q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)]
      exact L.mul p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)
    (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  obtain ⟨U', hU', hUK'⟩ := hK4' m
  refine ⟨U ×ˢ U', prod_mem_nhds hU hU', fun x hx h1 h2 => ?_⟩
  refine (L.acts x.1 h1 x.2 h2 φ hφ φ).2 ?_
  rw [← hloc x h1 h2 φ hφ]
  exact (hm x ⟨hUK _ hx.1 h1, hUK' _ hx.2 h2⟩).symm
end PositivityTheory.ThKF0
end
