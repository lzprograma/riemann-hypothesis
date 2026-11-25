module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Unfold0K
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasSatOfFamily
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.MemKFinOfFrameIntegral
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsUnitDetOfCartan
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasFrame
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ActsFormula
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxSec
public import Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
public import Development.WeilBound.ThetaLifts.LatticeBasics.CompactBound
public import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtExA
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtIntOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.SiegelWeilAnisoOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdMulRight
public import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtArch
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtCount
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtWitt
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat

/-! # Stab2CptK: Consolidated global theta-kernel definitions and proofs (Stab2CptK). -/
@[expose] public section
open UpperTheory.TP.W (GoodK)
open scoped TensorProduct NNReal Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open scoped Matrix TensorProduct NNReal
open Complex (I)

section
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.KCo
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.SplitFlip Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {t
  : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
def DictX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F
    E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E),
      GoodK σ B → (∃ r s, X.IsHerm σ B r s) →
    (∃ r s, W.IsSkew σ B r s) → M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι,
      M.IsLinBar B.ψ t 1 1 ι) ∧
      (∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g₀) ∧
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ ι, M.IsLinBar B.ψ t 1 1 ι →
        (∀ g ∈ UAt σ X (evFin F v), ∀ g₀ : GL (Fin n) (Fv F v), (mat g).map (piW t) = g₀ →
          Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)
theorem dictX_of_k (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hS : SecSt) (hU : ActsUniq) : DictX_k := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨⟨sec, h⟩, -⟩ := hS F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E},
    IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w)
      (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan
        w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm hM hA hB.std h hG M.co
  obtain ⟨hR, ⟨d', hd', hL⟩, -⟩ := hom
  obtain ⟨ε, -, hε, hε'⟩ := hG.sym
  refine ⟨⟨_, linBar_of_lm hA hU h hG hι₀⟩, fun g₀ => h.exists_ug hε hG.uA g₀, fun g₀ => h.exists_ug hε' hG.uB g₀,
    fun ι hι => ?_⟩
  have lm := lm_of_linBar hA hB.std h hG hι
  refine ⟨fun g hg g₀ e φ hφ => ?_, fun g hg g₀ e φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG.swap (lm.swap hd') hL.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Yᵀ)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, swH_apply, toM_ofM, smul_eq_mul]
      at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, apow_one, Matrix.mul_one]
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [← transpose_transpose (g₀.1ᵀ * Y), transpose_mul, transpose_transpose]
    rfl
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG lm hR.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Y)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, one_mul, apow_one, transpose_one, Matrix.one_mul]
    exact this
end PositivityTheory.KCo
end
end

section
namespace PositivityTheory.KCo
theorem dictX_proof_k : DictX_k := dictX_of_k model_existence cyclicity adjoint_statement section_statement
  action_uniqueness
end PositivityTheory.KCo
end

noncomputable section
namespace GlobalTheory.ThK.Dbl
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def FinLevel_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n :
    ℕ) (A : Spc F E m) (Y : Spc F E n), GoodK σ B → ∀ (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (K : Subgroup (G2 σ Y)),
    IsCompact (K : Set (G2 σ Y)) → ∀ Φ ∈ schA F κ, ∃ Λ : Set (Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      (∀ u ∈ Λ, (∀ i, evI F ((dd.e u).1 i) = 0) ∧ (∀ i, evI F ((dd.e u).2 i) = 0) ∧ ∀ k ∈ K, actB (cA σ) k u ∈ Λ) ∧
      (∀ u ∈ Λ, dd.rho B.ψ u Φ = Φ) ∧ ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧
        ∀ Ψ : (κ → AF F) → ℂ, (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) → ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) →
          ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0
end GlobalTheory.ThK.Dbl

namespace GlobalTheory.ThK.Dbl
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GroundTheory.Automorphic.GJMatrix GroundTheory.Global GlobalTheory.HeisSchA
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
theorem finLevel_k : FinLevel_k := by
  intro F E _ _ _ _ _ σ B m n A Y hB κ _ dd K hK Φ hΦ
  have lin : ∀ (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      actB (cA σ) k (epsF F • u) = epsF F • actB (cA σ) k u := fun k u => Matrix.smul_mul _ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ∀ {α β : Type} [Finite α] [Finite β], IsModuleTopology (AF F) (Matrix α β (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (_ → _ → AE F E))
  have c : Continuous fun y : ((κ → AF F) × (κ → AF F)) × G2 σ Y => dd.e (actB (cA σ) y.2 (dd.e.symm y.1)) :=
    (IsModuleTopology.continuous_of_linearMap dd.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap dd.e.symm.toLinearMap).comp continuous_fst).matrix_mul
        (Units.continuous_val.comp (continuous_subtypeVal.comp continuous_snd)).matrix_transpose)
  obtain ⟨s, hs, h⟩ := finite_values hB.std (hK.eventually_forall_of_forall_eventually
    (P := fun w k => schr B.ψ (epsF F • dd.e (actB (cA σ) k (dd.e.symm w))) Φ = Φ) fun k _ =>
      (c.tendsto' (0, k) 0 (by simp [actB])).eventually (level hB.std.1 hΦ))
  refine ⟨{u | epsF F • u = u ∧ ∀ k ∈ K, dd.rho B.ψ (actB (cA σ) k u) Φ = Φ}, fun u hu => ⟨fun i => ?_, fun i => ?_,
    fun k hk => ⟨by rw [← lin, hu.1], fun k' hk' => ?_⟩⟩, fun u hu => ?_, s, hs, fun Ψ hΨ => h Ψ fun w hw => ?_⟩
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · have := hu.2 _ (mul_mem hk' hk)
    simpa [actB, Matrix.mul_assoc] using this
  · simpa [actB] using hu.2 1 (one_mem _)
  · have := hΨ (epsF F • dd.e.symm w) ⟨by rw [smul_smul, epsF_sq], fun k hk => by
      rw [lin, Darboux.rho, map_smul]; exact hw k hk⟩
    rwa [Darboux.rho, map_smul, LinearEquiv.apply_symm_apply] at this
end GlobalTheory.ThK.Dbl
end

noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {κ β : Type}
  [Fintype κ] [Fintype β] {m n : ℕ}
variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E} {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (incM
  F Y.J)) κ} {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (κ ⊕ κ)} {om : G2 σ Y →*
  Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)} {K : Subgroup (G2 σ Y)}
theorem vac_kfin_k (hL : FinLevel_k) (hB : GoodK σ B) (hK : IsStab2
  B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) {ε} {Φ} (hΦ : Φ ∈ schA F (κ ⊕ κ))
    (hv : ∀ u u',
      At (evI F) u → At (evI F) u' → Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Φ = Complex.I • D (dd.e u) Φ) :
    Φ ∈ kfin om K := by
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := hL F E σ B m n A Y hB _ dd K hc Φ hΦ
  have radd : ∀ u (x y : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (x + y) = dd.rho B.ψ u x + dd.rho B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (c • x) = c • dd.rho B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {Ψ | Ψ ∈ schA F _ ∧ (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Ψ = Complex.I • D (dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _,
        fun _ _ _ _ _ => by simp only [D, DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [D] at e1 e2 ⊢
        rw [DP_add h.1 h'.1, DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [D] at e1 ⊢
        rw [DP_smul h.1, DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : κ ⊕ κ → AF F), (∀ i, evI F (y i) = 0) → pt x 0 + y = pt x (fn y) := fun x y hy => by
      rw [← pt_self (pt x 0 + y), nf_add, nf_pt, show nf y = 0 from funext hy, add_zero]
      exact congrArg (pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (pt 0 (fn z) i) = 0 := fun i => congrFun (evI_pt 0 (fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (pt (nf z) 0) (at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show fn (pt 0 (fn z)) = fn z from rfl, pt_self] at this
    obtain ⟨f, e⟩ := slice Ψ.2.1 (fn y)
    have g : Gs dd.e B.emb ε A.θ (th2 Y) f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (pt x (fn y))
      rwa [Pi.smul_apply, D, D, DP_pt e, DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show nf y = 0 from funext (s1 y hy), pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← actB_inv k u, ← actB_inv k u', ← om_D hB.std hs k (at_actB _ a) h.1, ← om_D hB.std hs k (at_actB _ b) h.1,
      ← map_smul]
    refine congrArg (om k) (h.2.2 _ _ (at_actB _ a) (at_actB _ b) fun w => ?_)
    have cm := (((hK k⁻¹).1 (inv_mem hk)).1 w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm
theorem box_kfin_k (hL : FinLevel_k) (hB : GoodK σ B) (hK : IsStab2
  B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (hd : IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d'
      dd)
    {P : Submodule ℂ (SInf F κ)} (hP : ∀ N : Submodule ℂ (SInf F κ), (∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → f ∈ N) →
      (∀ u, At (evI F) u → ∀ f ∈ N,
        dd0 (d'.e u) f ∈ N) → P ≤ N) {g₁ g₂} (s1 : g₁ ∈ SB (κ → Af F)) (s2 : g₂ ∈ SB (κ → Af F))
    {f₁ f₂} (h1 : f₁ ∈ P) (h2 : f₂ ∈ P) : boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂)) ∈ kfin om K := by
  let bx : SInf F κ → SInf F κ → (κ ⊕ κ → AF F) → ℂ := fun f f' => boxFun (pureA F f g₁) (star (pureA F f' g₂))
  have z1 : ∀ f', bx 0 f' = 0 := fun f' => funext fun z => by simp [bx, boxFun, pureA]
  have z2 : ∀ f, bx f 0 = 0 := fun f => funext fun z => by simp [bx, boxFun, pureA]
  have a1 : ∀ f g f',
    bx (f + g) f' = bx f f' + bx g f' := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul]
  have a2 : ∀ f f' g,
    bx f (f' + g) = bx f f' + bx f g := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul, mul_add]
  have c1 : ∀ (c : ℂ) f f',
    bx (c • f) f' = c • bx f f' := fun c f f' => funext fun z => by simp [bx, boxFun, pureA, mul_assoc]
  have c2 : ∀ (c : ℂ) f f', bx f (c • f') = star c • bx f f' := fun c f f' => funext fun z => by
    simp [bx, boxFun, pureA]; ring
  have at0 : At (evI F) (0 : Matrix (Fin m) (Fin n) (AE F E)) := fun _ _ => smul_zero _
  have d0 : ∀ f : SInf F κ, dd0 (d'.e 0) f = 0 := fun f => SchwartzMap.ext fun x => by
    simp [dd0, dop_apply, show nf (0 : κ → AF F) = 0 from funext fun _ => evI_zero, linForm_apply]
  have atc : ∀ {u₁ u₂ : Matrix (Fin m) (Fin n) (AE F E)},
    At (evI F) u₁ → At (evI F) u₂ → At (evI F) (Matrix.fromCols u₁ u₂) :=
    fun h1 h2 s hs => by
      ext i (j | j)
      exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]
  have base : ∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → ∀ ε' f', Gs d'.e B.emb ε' A.θ Y.θ f' → bx f f' ∈ kfin om K := by
    intro ε f hf ε' f' hf'
    by_cases e : f = 0
    · rw [e, z1]; exact zero_mem _
    by_cases e' : f' = 0
    · rw [e', z2]; exact zero_mem _
    have hf'' := hf.same hB.cm hf' e e'
    refine vac_kfin_k (ε := ε) hL hB hK hc hs (box_mem (Submodule.subset_span ⟨f, g₁, s1,
      rfl⟩) (Submodule.subset_span ⟨f', g₂, s2, rfl⟩))
      fun u u' a b c => ?_
    have al : ∀ {v : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)},
      At (evI F) v → At (evI F) v.toCols₁ ∧ At (evI F) v.toCols₂ := fun h =>
      ⟨fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inl j),
        fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inr j)⟩
    have r1 : Rel B.emb ε A.θ Y.θ u.toCols₁ u'.toCols₁ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inl j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have r2 : Rel B.emb ε A.θ Y.θ (-u.toCols₂) u'.toCols₂ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inr j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have n2 : dd0 (d'.e (-u.toCols₂)) f' = -dd0 (d'.e u.toCols₂) f' := SchwartzMap.ext fun x => by
      have ng : ∀ y : κ → AF F,
        nf (-y) = -nf y := fun y => funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _
      simp only [dd0, map_neg, Prod.fst_neg, Prod.snd_neg, ng, dop_apply, neg_apply, linForm_apply,
        Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib]
      push_cast
      ring
    rw [← u.fromCols_toCols, ← u'.fromCols_toCols, D_box hB.std hd (al a).1 (al a).2 f f' s1 s2,
      D_box hB.std hd (al b).1 (al b).2 f f' s1 s2, hf _ _ (al a).1 (al b).1 r1,
      hf'' _ _ (fun s hs => by rw [smul_neg, (al a).2 s hs, neg_zero]) (al b).2 r2, n2, smul_neg, ← neg_smul]
    change bx _ _ + bx _ _ = _ • (bx _ _ + bx _ _)
    rw [c1, c2, smul_add]
    simp
  refine hP ⟨⟨⟨{f' | ∀ f ∈ P, bx f f' ∈ kfin om K}, fun h h' f hf => a2 f _ _ ▸ add_mem (h f hf) (h' f hf)⟩,
    fun f _ => z2 f ▸ zero_mem _⟩, fun c _ h f hf => c2 c f _ ▸ Submodule.smul_mem _ _ (h f hf)⟩ (fun ε' f' hf' => ?_)
    (fun u hu f' h f hf => ?_) h2 f₁ h1
  · refine hP ⟨⟨⟨{f | bx f f' ∈ kfin om K}, fun h h' => by
      rw [Set.mem_ofPred_eq, a1]; exact add_mem h h'⟩, by rw [Set.mem_ofPred_eq, z1]; exact zero_mem _⟩,
      fun c _ h => by rw [Set.mem_ofPred_eq, c1]; exact Submodule.smul_mem _ _ h⟩ (fun ε f hf => base ε f hf ε' f' hf')
        fun u hu f h => ?_
    have := D_kfin hB.std hs (atc hu at0) h
    rw [D_box hB.std hd hu at0 f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rw [z2, add_zero] at this
    exact this
  · have := D_kfin hB.std hs (atc at0 hu) (h f hf)
    rw [D_box hB.std hd at0 hu f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rwa [z1, zero_add] at this
end GlobalTheory.ThK.Dbl.Box

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.ThK.Dbl
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
def Stab2Cpt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (Y : Spc F E n) r s, GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → IsCompact (K : Set (G2 σ Y))
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y :
  Spc F E n} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {z s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ
  Y.J →* G2 σ Y}
theorem kpair_cont_k {B : Base F E} {r s : ℕ} (hB : GoodK σ B) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew
  σ B r s) (h0 : min r s = 0)
    (c : Cpt σ Y.J) (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x,
      0 < a x) (cf : Continuous f) (hf : Law χ z f)
    {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ Y.J) D μ) {t₀ : ℝ} (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) :
    (∀ φ, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U) ∧ ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧
      Integrable (fun g => flat a f s₀ s (e (1, g)) * detInv χ g) μ ∧ ∀ φ, IsRapid φ → kpair χ e μ D (Ê s) φ =
        ∫ g, flat a f s₀ s (e (1, g)) * detInv χ g * pet μ D (fun h => φ (h * g)) φ ∂μ := by
  have hJ := aniso_of_k hB hY h0
  obtain ⟨t₁, half⟩ := hE.half
  have := c.sc; have := c.lc
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using c.fin _ _ hμ hD⟩
  have bc : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → An.BC φ := fun h => ⟨h.1, c.bdd h.1 h.2.1⟩
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ ratU σ Y.J, ∀ δ ∈ ratU σ Y.J, ∀ g g', Ê s (e (γ * g, δ * g')) = Ê s (e (g,
    g')) := fun s hs γ hγ δ hδ g g' =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1, by
      rw [← Prod.mk_mul_mk, map_mul]; exact (hf.flat ha a0 s).eis_inv hχ hJ he (half s hs).2 hγ hδ _⟩) hs
  have ck : ∀ s ∈ U, An.BC fun y : UA σ Y.J × UA σ Y.J => Ê s (e y) * detInv χ y.2 := fun s hs =>
    An.BC.mul ⟨(cE s hs).comp ce, c.bdd₂ c ((cE s hs).comp ce) (iv s hs)⟩
      ⟨(continuous_detInv hχ).comp continuous_snd, 1, fun y => (norm_detInv _ _).le⟩
  have hol : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U := fun {φ} h => by
    have b := ((bc h).comp (continuous_snd (X := UA σ Y.J))).mul ((bc h).comp continuous_fst).star
    refine An.diffOn_integral hE.isOpen (fun s hs => ((ck s hs).mul b).1.aestronglyMeasurable)
      (fun y => ((hE.hol _).mul_const _).mul_const _) fun S hS cS => ?_
    obtain ⟨Ω, hΩ, cov⟩ := c.cov
    obtain ⟨C, hC⟩ := (cS.prod ((hΩ.prod hΩ).image ce)).exists_bound_of_continuousOn
      (hE.cont.mono (Set.prod_mono hS (Set.subset_univ _)))
    obtain ⟨C', hC'⟩ := b.2
    refine ⟨C * C', fun s hs y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    obtain ⟨δ, hδ, h2⟩ := cov y.2
    have := hC (s, e (γ * y.1, δ * y.2)) ⟨hs, _, ⟨h1, h2⟩, rfl⟩
    rw [iv s (hS hs) γ hγ δ hδ] at this
    rw [norm_mul, norm_mul, norm_detInv, mul_one]
    exact mul_le_mul this (hC' y) (norm_nonneg _) ((norm_nonneg _).trans this)
  refine ⟨fun _ => hol, max t₁ (t₀ + s₀.re - z.re), fun s hs => ?_⟩
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt hs)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s - s₀ + z).re (by have := (le_max_right _ _).trans_lt hs; simp; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  exact ⟨u, i2, fun φ h => An.far_right _ μ (ck s u) (bc h) i2
    (unfold0_k F E σ B n Y r _ hB hY h0 χ e hχ he _ _ _ cs (cE s u) sm (hf.flat ha a0 s) μ D hμ hD i1 _ h)⟩
end GlobalTheory.ThK.Dbl

namespace GlobalTheory.ThK.Dbl.Box
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {κ β : Type}
  [Fintype κ] [Fintype β] {m n : ℕ}
variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k (hL : FinLevel_k) (hC :
  Stab2Cpt_k) : BoxSecX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl
    hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have hmem := n2 uᵀ (tr hu) f hf
    rwa [ht] at hmem
end GlobalTheory.ThK.Dbl.Box
end

noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.ThKG.Tow St
attribute [local instance] ae_ring ae_t2 ae_smul
theorem stab2Cpt_k : Stab2Cpt_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  obtain ⟨hL, c, c0, hc⟩ : Y.L.IsFullLattice E ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ w, IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) :=
    hY.elim (fun h => ⟨h.lat, 1, one_ne_zero, fun w => by simpa using h.cartan w⟩) fun h => ⟨h.lat, _,
      Complex.I_ne_zero, h.cartan⟩
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  choose C hC h using fin_bound (F := F) Y hL
  choose R hR using fun w => cartan_bound2 (hc w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtypeVal
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have cl := (isCompact_latHat Y hL.fg).isClosed
  have key : ∀ k ∈ K, mat2 k ∈ Set.univ.pi fun i => Set.univ.pi fun j =>
      (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C (Sum.elim id id i) (Sum.elim id id j) := fun k hk
        i _ j _ => by
    obtain ⟨k1, k2⟩ := (hK k).1 hk
    rw [eΦ (mat2 k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      refine hR w ((mat2 k).map (piInf (B.emb w))) ?_ (k1 w) i j
      have e := congrArg (fun X => c • Matrix.map X (piInf (B.emb w)))
        (show (mat2 k)ᵀ * dbl (incM F Y.J) * (mat2 k).map (cA σ) = dbl (incM F Y.J) from k.2)
      have d : c • (dbl (incM F Y.J)).map (piInf (B.emb w)) = dbl (c • Y.J.map (B.emb w).1) := by
        ext (a | a) (b | b) <;> simp [dbl, incM, Levi.piInf_incl]
      have d2 : ((mat2 k).map (cA σ)).map (piInf (B.emb w)) = ((mat2 k).map (piInf (B.emb w))).map star :=
        Matrix.ext fun a b => Levi.piInf_cA hB.cm _ _
      simp only [Matrix.map_mul] at e
      rwa [← Matrix.smul_mul, ← Matrix.mul_smul, d, d2] at e
    · have a := fun y hy => k2 y 0 hy (zero_mem _) k (.inl rfl)
      have b := fun y hy => k2 0 y (zero_mem _) hy k (.inl rfl)
      rw [← Matrix.fromBlocks_toBlocks (mat2 k)] at a b
      simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero, zero_add]
        at a b
      rcases i with i | i <;> rcases j with j | j
      exacts [h i j _ fun y hy => (a y hy).1, h i j _ fun y hy => (b y hy).1, h i j _ fun y hy => (a y hy).2,
        h i j _ fun y hy => (b y hy).2]
  refine isCompact_of_units _ (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul
    continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const) _ ?_ _
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC _ _)) fun k hk => ⟨key k hk, key _ (inv_mem hk)⟩
  rw [show (K : Set (G2 σ Y)) = {k | _} from Set.ext hK]
  simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  simp only [Set.ofPred_and, Set.ofPred_forall]
  have v : ∀ {f : G2 σ Y → G2 σ Y}, Continuous f → ∀ z, IsClosed ({k | (mat2 (f k) *ᵥ z) ∘ Sum.inl ∈ latHat Y} ∩
      {k | (mat2 (f k) *ᵥ z) ∘ Sum.inr ∈ latHat Y}) := fun hf z =>
    have t := (hm.comp hf).matrix_mulVec (continuous_const (y := z))
    (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t)).inter
      (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t))
  exact (isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))).inter
    (isClosed_iInter fun z => isClosed_iInter fun z' => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      (v continuous_id _).inter (v continuous_inv _))
end GlobalTheory.ThK.Dbl
end

noncomputable section
namespace GlobalTheory.ThK.Dbl.Hgt
open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.UG GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl
open PositivityTheory.ThKH.Iwas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v :
  Pl F}
theorem hasSat_good_k {B : Base F E} (hB : GoodK σ B) (v : Pl F) : HasSat (intLoc F E v) (Fin n)
  := by
  have e : ∀ (K : Type) [Field K] [NumberField K] (u : Pl K) (a : Fv K u),
      a ∈ (algebraMap (u.adicCompletionIntegers K) (Fv K u)).range ↔ a ∈ u.adicCompletionIntegers K :=
    fun _ _ _ _ a => ⟨by rintro ⟨x, rfl⟩; exact x.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have hc := hB.cm
  rcases GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · refine hasSat_of_family (O := v.adicCompletionIntegers F) (I := Bool)
      (fun i => cond i (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v))
      (fun y z h => split_ext hc τ (h true) (h false))
      (fun f => ⟨(splitAlgEquiv hc τ).symm (f true, f false), fun i => ?_⟩) _ (fun y => ?_) _
    · cases i
      · exact splitProj_comp_symm hc τ _
      · exact splitProj_symm hc τ _
    · rw [mem_intLoc_iff_split hc τ, Bool.forall_bool]
      simp only [Bool.cond_false, Bool.cond_true, e]
      exact and_comm
  · have h := (InertChart.under_eq_iff hw w).2 rfl
    refine hasSat_of_family (O := w.adicCompletionIntegers E) (I := Unit) (fun _ => toCompl h)
      (fun y z e => (InertChart.toCompl_bijective hw h).1 (e ())) (fun f => ?_) _ (fun y => ?_) _
    · obtain ⟨y, hy⟩ := (InertChart.toCompl_bijective hw h).2 (f ())
      exact ⟨y, fun _ => hy⟩
    · rw [InertChart.mem_intLoc_iff hw h]
      exact ⟨fun hy _ => ⟨⟨_, hy⟩, rfl⟩, fun hy => by obtain ⟨x, hx⟩ := hy (); rw [← hx]; exact x.2⟩
theorem hasIwasawa_fin'_k {B : Base F E} (hB : GoodK σ B) {Y : Spc F E n} {r s : ℕ} (hY :
  Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) {ξ : E} (hξ : ξ ≠ 0) (hh : ∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) (v : Pl F) :
    HasIwasawa σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ)) (GlobalTheory.Doubling.KFin σ _ Y.L v) := by
  have hσ := cm_conj_conj hB.cm
  have hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  obtain ⟨δ, h0, G', hG', b1, b2⟩ : ∃ δ : E, δ ≠ 0 ∧ ∃ G' : Matrix (Fin n) (Fin n) E,
    G' * (P.1ᵀ * Y.J * P.1.map σ) = 1 ∧
      (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * Y.J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by
    rcases hY with h | h
    · exact ⟨1, one_ne_zero, gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
        isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2⟩
    · obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
      exact ⟨δ, d0, gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  let ι := inclR (F := F) (E := E) (Fv F v)
  let l : (Fv F v ⊗[F] E)ˣ := Units.map ι.toMonoidHom (Units.mk0 (δ * ξ) (mul_ne_zero h0 hξ))⁻¹
  have e : l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P) = (δ⁻¹ • Gᵀ).map ι := by
    have e1 : locGram σ (ξ • Y.Jᵀ) (bc ι P) = (ξ • Gᵀ).map ι := by
      rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_smul,
        ← Matrix.smul_mul,
        ← Matrix.mul_assoc, Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e1]
    ext i j
    change ι (δ * ξ)⁻¹ * ι (ξ * G j i) = ι (δ⁻¹ * G j i)
    rw [← map_mul]; congr 1; field_simp
  refine hasIwasawa_of_frame' σ hσ rfl hh (intLoc F E v) ((1 : Fv F v) ⊗ₜ[F] (t : E)) (tmul_mem_intLoc (one_mem _) t) ?_
    (fun z hz => sigR_mem_intLoc σ hz) (bc ι P) l (fun i j => ?_) ⟨(δ • G'ᵀ).map ι, fun i j => (b2 j i).mem, ?_⟩
    (hasSat_good_k hB v) _ fun k => mem_KFin_of_frame_integral σ _ (Frames.frame_of_rational P h1 h2) k
  · change (1 : Fv F v) ⊗ₜ[F] (t : E) + (1 : Fv F v) ⊗ₜ[F] (σ t) = 1
    rw [← TensorProduct.tmul_add, ht]
    rfl
  · change (l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P)) i j ∈ _
    rw [e]
    exact (b1 j i).mem
  · rw [e, ← Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h0, one_smul,
      ← Matrix.transpose_mul,
      mul_eq_one_comm.1 hG', Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]
end GlobalTheory.ThK.Dbl.Hgt

namespace GlobalTheory.ThK.Dbl.Hgt
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.WeilM
open GlobalTheory.CompanionTheory.IwaDbl.FrameCore
open Formalism.UG (cT bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y :
  Spc F E n}
section
variable {B : Base F E}
theorem exists_scal_k (hB : GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨
  Y.IsSkew σ B r s) :
    ∃ ξ : E, ξ ≠ 0 ∧ (∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) ∧ ∀ w, ∃ (M : Matrix (Fin n) (Fin n) ℂ) (r : ℝ),
      Mᴴ = M ∧
      IsCartan M (Y.θ w) ∧ r ≠ 0 ∧ (ξ • Y.Jᵀ).map (B.emb w).1 = (r : ℂ) • Mᵀ := by
  have hc := hB.cm
  rcases hY with h | h
  · refine ⟨1, one_ne_zero, fun i j => by simpa using h.herm j i, fun w => ⟨_, 1, ?_, h.cartan w, one_ne_zero, ?_⟩⟩
    · exact Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))
    · ext i j; simp
  · obtain ⟨x, hx⟩ : ∃ x, x - σ x ≠ 0 := by
      by_contra! e
      have := hc.2.1
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
          (hc.2.2.2 τ y).symm.trans (congrArg τ (sub_eq_zero.1 (e y)).symm))))
    have hs : σ (x - σ x) = -(x - σ x) := by rw [map_sub, cm_conj_conj hc, neg_sub]
    refine ⟨_, hx, fun i j => ?_, fun w => ?_⟩
    · change σ (_ * Y.J i j) = _ * Y.J j i
      rw [map_mul, hs, h.skew, neg_mul_neg]
    · have h1 := hc.2.2.2 (B.emb w).1 (x - σ x)
      rw [hs, map_neg] at h1
      have h2 : (B.emb w).1 (x - σ x) = ((B.emb w).1 (x - σ x)).im * I := by
        have := congrArg Complex.re h1
        simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
        exact Complex.ext (by simp only [Complex.mul_I_re, Complex.ofReal_im]; linarith) (by simp)
      refine ⟨_, ((B.emb w).1 (x - σ x)).im, Matrix.ext fun i j => ?_, h.cartan w, fun e => hx ?_,
        Matrix.ext fun i j => ?_⟩
      · change star (I * (B.emb w).1 (Y.J j i)) = I * (B.emb w).1 (Y.J i j)
        rw [star_mul', ← hc.2.2.2, h.skew]; simp
      · rw [e] at h2
        exact (map_eq_zero _).1 (h2.trans (by simp))
      · change (B.emb w).1 (_ * Y.J j i) = _ * (I * (B.emb w).1 (Y.J j i))
        rw [map_mul, ← mul_assoc, ← h2]
theorem iwasawa2_k (hB : GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ
  B r s) (x : G2 σ Y) :
    ∃ p : siegelOf (Equiv.refl (Fin n ⊕ Fin n)) (UG (cA σ) (dbl (incM F Y.J))).subtype, ∃ k ∈ stab2 σ Y B,
      x = p * k := by
  have hL := hY.elim (·.lat) (·.lat)
  obtain ⟨ξ, hξ, hh, hw⟩ := exists_scal_k hB hY
  choose M r h1 h2 h3 h4 using hw
  choose b hb hb' using fun w => exists_arch hB.cm (B.emb w) (h1 w) (isUnit_of_cartan (h2 w)) (h2 w) (h3 w) (h4 w)
  obtain ⟨a, -, ha⟩ := Frames.exists_isLatticeFrame_of_arch Y.L b
  obtain rfl : b = fun w => bc (compInf F E w) a := (funext ha).symm
  obtain ⟨g, rfl⟩ := back_surj hξ x
  obtain ⟨p, k, hk, rfl⟩ := HasIwasawa.adelic (hasIwasawa_fin'_k hB hY (det_ne hY) hξ hh) hb g
  have k2 := keeps_back hL.fg hξ (mem_KAd.1 (inv_mem hk)).1
  rw [map_inv] at k2
  exact ⟨⟨_, back_mem_par hξ p.2⟩, back σ Y hξ k, ⟨fun w => back_comm hξ _ ((hb' w _).1 ((mem_KAd.1 hk).2 w)),
    keeps_back hL.fg hξ (mem_KAd.1 hk).1, k2⟩, map_mul _ _ _⟩
theorem hgtEx_core_k (hB : GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew
  σ B r s)
    (hK : IsCompact (stab2 σ Y B : Set (G2 σ Y))) :
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h')) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hI := iwasawaOf_of_isCompact (ν := absE F E) continuous_subtypeVal continuous_absE hK (iwasawa2_k hB hY)
  refine ⟨⟨_, fun x => hgtOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype (absE F E) (stab2 σ Y B) x,
    isStab2_stab2 B,
    ⟨fun x => ?_, fun p t hp k hk => ?_⟩,
    NNReal.continuous_coe.comp (hI.continuous_hgtOf continuous_subtypeVal continuous_absE hK), fun x => hgtOf_pos x⟩,
    emb2 σ Y, ((continuous_blkGL _).comp (continuous_subtypeVal.prodMap continuous_subtypeVal)).subtype_mk _,
      fun _ _ => rfl⟩
  · obtain ⟨p, h⟩ := iwasawa2_k hB hY x
    exact ⟨p, leviOf _ _ p, isPar_iff.2 ⟨mem_siegelOf.1 p.2, rfl⟩, h⟩
  · obtain ⟨h1, h2⟩ := isPar_iff.1 hp
    have := hI.hgtOf_mul ⟨p, mem_siegelOf.2 h1⟩ hk
    rw [show t = leviOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype ⟨p,
      mem_siegelOf.2 h1⟩ from Units.ext h2.symm]
    exact congrArg NNReal.toReal this
end
end GlobalTheory.ThK.Dbl.Hgt

namespace GlobalTheory.ThK.Dbl
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdelicU
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.Doubling GlobalTheory.WeilM Hgt
theorem hgtEx_of_k (hK : Stab2Cpt_k) : HgtEx_k := fun F E _ _ _ _ _ σ B n Y r s hB hY =>
  Hgt.hgtEx_core_k hB hY (hK F E σ B n Y r s hB hY _ (isStab2_stab2 B))
theorem hgtInt_of_k (hC : Stab2Cpt_k) : HgtInt_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K a e hK ha he μ hμ
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
  have : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  have cK := hC F E σ B n Y r s hB hY K hK
  obtain ⟨⟨K', a', hK', ha', ca, a0⟩, e', ce, he'⟩ := hgtEx_of_k hC F E σ B n Y r s hB hY
  obtain rfl : K = K' := Subgroup.ext fun k => (hK k).trans (hK' k).symm
  obtain rfl : a = a' := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha'.val p t hp k hk]
  obtain rfl : e = e' := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he x.1 x.2).trans (he' x.1 x.2).symm))
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  let T : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₁
  let T' : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₂
  have cm : Continuous fun k : G2 σ Y => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) :=
    ((Units.continuous_val.comp continuous_subtypeVal).comp continuous_inv).matrix_mul continuous_const
  have cT : Continuous T := cm.matrix_submatrix _ _
  have cT' : Continuous T' := cm.matrix_submatrix _ _
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
  let c := (Module.Free.chooseBasis (AF F) (Matrix (Fin n) (Fin n) (AE F E))).equivFun
  obtain ⟨R, C, b, h1, h2, h3,
    h4⟩ := count_ad (E := E) hB.cm.1 c (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap) (UG (cA σ) (incM F Y.J))
    (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const)
    ((cK.image ((cc.comp cT'.matrix_det).smul (cT.matrix_mul cT'.matrix_adjugate))).union
      (cK.image ((cc.comp cT.matrix_det).smul (cT'.matrix_mul cT.matrix_adjugate))))
    (cK.image (continuous_norm_tens.comp cT.matrix_det)) μ
  have key : ∀ g : UA σ Y.J, ∃ k ∈ K, ∃ t : GL (Fin n) (AE F E), a (e (1,
    g)) = absE F E (Matrix.GeneralLinearGroup.det t) ∧
      T k = t.1 ∧ T' k = mat g⁻¹ * t.1 := fun g => by
    obtain ⟨p, t, hp, k, hk, h⟩ := ha.iwa (e (1, g))
    have e1 : k⁻¹ = e (1⁻¹, g⁻¹) * p := by rw [← Prod.inv_mk, map_inv, h]; group
    have hp' : (mat2 p * diagCols (E := AE F E) (Fin n)) = (diagCols (E := AE F E) (Fin n) * t.1) := hp
    have e2 : (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) = Matrix.fromRows t.1 (mat g⁻¹ * t.1) := by
      rw [e1, show mat2 (e (1⁻¹, g⁻¹) * p) = mat2 (e (1⁻¹, g⁻¹)) * mat2 p from rfl, Matrix.mul_assoc, hp', he, inv_one,
        show mat (1 : UA σ Y.J) = 1 from rfl, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
      simp
    exact ⟨k, hk, t, by rw [h, ha.val p t hp k hk], congrArg Matrix.toRows₁ e2, congrArg Matrix.toRows₂ e2⟩
  refine integrable_of_count μ (ca.comp (ce.comp (Continuous.prodMk_right 1))).measurable (fun g => a0 _) (R := R) h1
    (fun g => ?_)
    h2 b fun j => (measure_mono fun g hg => ?_).trans (h4 j)
  · obtain ⟨k, hk, t, e1, e2, -⟩ := key g
    exact e1.trans_le (h3 _ ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩)
  · obtain ⟨k, hk, t, e1, e2, e3⟩ := key g
    have hd : (mat g⁻¹).det * (cA σ).toRingHom (mat g⁻¹).det = 1 := by
      have h := congrArg Matrix.det (show (mat g⁻¹)ᵀ * incM F Y.J * (mat g⁻¹).map (cA σ) = incM F Y.J from (g⁻¹).2)
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show ((mat g⁻¹).map (cA σ)).det = (cA σ).toRingHom (mat g⁻¹).det from ((cA σ).toRingHom.map_det _).symm] at h
      refine (isUnit_det_JR (R := AF F) (det_ne hY)).mul_left_cancel ?_
      change (incM F Y.J).det * _ = (incM F Y.J).det * _
      linear_combination h
    obtain ⟨q1, q2⟩ := Hgt.graph_alg (cA σ).toRingHom (g := mat g) g.1.mul_inv e3 hd
    have q : ∀ X : Matrix (Fin n) (Fin n) (AE F E),
      Algebra.norm (AF F) t.1.det • X = (t.1.det * (cA σ).toRingHom t.1.det) • X :=
      fun X => by rw [← algebraMap_smul (AE F E), algebraMap_norm_eq hB.cm, ← cA_eq]; rfl
    refine ⟨Matrix.GeneralLinearGroup.det t, ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩,
      e1 ▸ hg,
      .inl ⟨k, hk, Eq.symm ((q _).trans (q1.trans ?_))⟩, .inr ⟨k, hk,
        Eq.symm ((q _).trans (q2.trans ?_))⟩⟩ <;> rw [← e2] <;> rfl
end GlobalTheory.ThK.Dbl
end

noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {κ : Type}
  [Fintype κ] {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {B : Base F E} {ψ : AddChar (AF F) ℂ}
variable {dd} {χ : Chr F E} {om S l}
theorem sw_transl_k (h1 : SiegelWeilStd_k) (h2 : FrameConj_k) {r
  s r' s'} (hB : GoodK σ B) (hm : 1 ≤ m) (hn : 1 ≤ n) (h0 : min r s = 0)
    (hA : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') (hχ : IsHecke F E χ)
    (hc : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) {dd om S l}
    (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l) {K a} (hK : IsStab2 B K) (ha : IsHgt K a)
    {μ : Measure (UA σ A.J)} {D : Set (UA σ A.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ A.J) D μ)
    {Φ} (hΦ : Φ ∈ kfin om K) : EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
      fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  obtain ⟨N, _, n0, n1, n2⟩ := hΦ
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r' s' hB (hA.symm.imp And.right And.right) K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ _root_.GlobalTheory.ThK.Dbl.absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ _root_.GlobalTheory.ThK.Dbl.absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul,
        map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have mul : ∀ x y Ψ, om x (om y Ψ) = om (x * y) Ψ := fun x y Ψ => by rw [map_mul, mul_apply_eq_comp]
  intro x
  obtain ⟨e, e1, ⟨t₁, e2⟩, e3,
    e4⟩ := h1 F E σ B m n A Y r s r' s' hB hm hn h0 hA χ hχ hc _ dd om S l h b K₀ _ hb hK₀ ha₀ μ D hμ hD
    (om p⁻¹ Φ) (h.weil.2.1.pres _ _ (n0 n1)) (Submodule.finiteDimensional_of_le (S₂ := N.map (om p⁻¹))
      (Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, n2 _ (hk' k k.2) Φ n1, by simp only [mul]; congr 2; group⟩))) (x * p)
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) :=
    (differentiable_id.const_sub _).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine ⟨fun z => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) * e z, fun z hz => (dc.analyticAt z).meromorphicAt.mul (e1 z hz),
    ⟨t₁, fun z hz => ?_⟩, (dc.analyticAt _).mul e3, ?_⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mpr ((e2 z hz).mul_left ((d : ℂ) ^ (((m : ℂ) - n) / 2 - z)))
    simp only [eisTerm, flat, mul, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · simp
      only [e4, sub_self, Complex.cpow_zero, one_mul, ← dbl_comm hB.std h hp.inv _ (n0 n1), mul, mul_inv_cancel_right]
theorem _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of_k (h1 : SiegelWeilStd_k) (h2 :
  FrameConj_k) (hL : FinLevel_k) (hC :
  Stab2Cpt_k) :
    SiegelWeilAniso_k := by
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hc dd om S l hd h K a hK ha Φ₁ p1 Φ₂ p2
    refine sw_transl_k h1 h2 hB hm hn h0 (.inl ⟨hA, hY⟩) hχ hc h hK ha hM.haar hM.dom
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin_k hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
    · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf
  · intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd' hX hW h0 hM χ hχ hc dd om S l ⟨d', ht,
      hd⟩ h K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
    have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
      rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
    refine sw_transl_k h1 h2 hB hd' hn h0 (.inr ⟨hW, hX⟩) hχ hc h hK ha hμ hD
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · have er : Rel B.emb ε X.θ W.θ uᵀ u'ᵀ := fun w => by
        simpa [Matrix.transpose_map, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc] using congrArg
          Matrix.transpose (e w)
      have he := hε uᵀ u'ᵀ (tr hu) (tr hu') er _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
      have ht1 : d'.e u = M.co.e uᵀ := by simpa using ht uᵀ
      have ht2 : d'.e u' = M.co.e u'ᵀ := by simpa using ht u'ᵀ
      rw [ht1, ht2]
      change dop (aOf M u'ᵀ) (lOf M u'ᵀ) f = I • dop (aOf M uᵀ) (lOf M uᵀ) f
      exact he
    · rw [actsD_unique' M hB.std hu e]
      have := n2 uᵀ (tr hu) f hf
      rwa [ht] at this
end GlobalTheory.ThK.Dbl.Box
end

namespace GlobalTheory.ThK.Dbl
theorem hgtEx_k : HgtEx_k := hgtEx_of_k stab2Cpt_k
end GlobalTheory.ThK.Dbl
