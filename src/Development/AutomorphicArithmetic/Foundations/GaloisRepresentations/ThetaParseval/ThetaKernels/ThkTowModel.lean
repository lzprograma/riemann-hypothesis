module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowFinal
public import Development.WeilBound.ThetaLifts.TowerModels.DetHerm
public import Development.WeilBound.ThetaLifts.TowerModels.ExistsHaarOfIsCompact
public import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.WeilBound.ThetaLifts.TowerModels.StabCpt
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AdelicSchrodingerTensorEqLocalOfSupportedAt
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ContinuousAddCharSymplecticSelfPairingPlaceCoord
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EqAdeleSupportedAtFinitePlaceOfSupportedAt
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

/-! # ThkTowModel: Consolidated global theta-kernel definitions and proofs (ThkTowModel). -/
@[expose] public section

open UpperTheory.TP.W (GoodK)
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
open scoped ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels TensorProduct
open _root_.GlobalTheory
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open scoped TensorProduct NNReal Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At cA incM)
open GlobalTheory.WeilM (Darboux symp)

section
namespace Tw
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain
  NumberField MeasureTheory Matrix Classical _root_.GlobalTheory
theorem exists_int_add_conj_eq_one_of_base_good_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), GoodK σ B → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  have := hB.unram
  exact exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
end Tw
end

noncomputable section
open Classical Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Matrix MeasureTheory
  NumberField
open GlobalTheory in
theorem Tw.RatDarboux.exists_rational_darboux_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), GoodK σ B → X.IsHerm σ B r s →
      Y.IsSkew σ B r' s' →
    ∃ co : Darboux (symp (R := AF F)
      (cA σ) (-1)
      (incM F X.J)
      (incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun k => algebraMap F (AF F) (y k),
          fun k => algebraMap F (AF F) (z k)) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hY' : Y.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hY.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det Y.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  exact Tw.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ hσ hX.herm hY.skew hX' hY'
end

section
open Classical Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Matrix MeasureTheory
  NumberField
theorem Tw.RatDarboux.exists_rational_darboux_of_isGood_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : Darboux (symp (R :=
      AF F) (cA σ) (-1)
      (incM F X.J)
      (incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e
      (incM F x) = (fun k => algebraMap F (AF F) (y k),
      fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => _root_.Tw.RatDarboux.exists_rational_darboux_k _ B X Y r s r' s' hB hX hY
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain
  NumberField MeasureTheory Matrix Classical
noncomputable section
namespace Tw.LatVacArith
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
      B.ψ (b * symp (R := AF F) (cA σ)
        (inclR (AF F) (θ : E))
        (incM F X.J)
          (incM F Y.J) γ γ') = 1 := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY v θ b hb γ hγ γ' hγ'
  have step : ∀ z' ∈ {z | ∃ a : AF F,
    At (GlobalTheory.AdelicU.evFin F v) a ∧ GlobalTheory.AdelicU.evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ x ∈ X.L, ∃ y ∈ Y.L,
        z = a • incM F (Matrix.vecMulVec x y)},
      ∀ γ ∈ latAtV X Y v,
        B.ψ (b * symp (R := AF F) (cA σ)
        (inclR (AF F) (θ : E))
        (incM F X.J)
          (incM F Y.J) γ z') = 1 := by
    intro z' hz' γ hγ
    obtain ⟨a', -, ha', x', hx', y', hy', rfl⟩ := hz'
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
      exact psi_gen σ B X Y hX hY hB.std v θ b hb ha hav ha' hx hx' hy hy'
    | zero => rw [symp_zero_left, mul_zero, AddChar.map_zero_eq_one]
    | add x y _ _ hx hy =>
      rw [symp_add_left, mul_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
    | neg x _ hx =>
      rw [symp_neg_left, mul_neg, AddChar.map_neg_eq_inv, hx, inv_one]
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz => exact step z hz γ hγ
  | zero => rw [symp_zero_right, mul_zero, AddChar.map_zero_eq_one]
  | add x y _ _ hx hy =>
    rw [symp_add_right, mul_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
  | neg x _ hx =>
    rw [symp_neg_right, mul_neg, AddChar.map_neg_eq_inv, hx, inv_one]
end Final
end Tw.LatVacArith
end
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain
  NumberField MeasureTheory Matrix Classical
noncomputable section
namespace Tw.VacCocycle
theorem psi_half_symp_add_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E
  →ₐ[F] E}
    (B : Base F E), GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E,
      (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR
        (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
          (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
            (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
            (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : ∀ e : E,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ
    e) := fun e => rfl
  have hsw := symp_swap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hc (JA :=
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (JB :=
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)
    (fun i j => by simp
      only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hX.herm])
    (fun i j => by simp
      only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hY.skew, map_neg])
    (ξ := inclR (F := F) (AF F) (θ : E)) (by rw [hi, ← map_add (f := _), hθ, map_one]) γ γ'
  have h1 := _root_.Tw.LatVacArith.psi_symp_latAtV_k σ B X Y r s r' s' hB hX hY v θ 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have h2 := _root_.Tw.LatVacArith.psi_symp_latAtV_k σ B X Y r s r' s' hB hX hY v (-1) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have hm : inclR (F := F) (AF F) ((-1 : 𝓞 E) : E) = -1 := by
    rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one]
  rw [hm] at h2
  rw [Tw.LatVacArith.symp_add_left, Tw.LatVacArith.symp_add_right, Tw.LatVacArith.symp_add_right, hsw,
    ← mul_one (_ * _ * _), ← h1, ← mul_one (_ * _ * _ * _), ← h2]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  have h : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = t at h ⊢
  linear_combination (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA
    σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') * h
end Tw.VacCocycle
end
end

noncomputable section
namespace GlobalTheory.ThK
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Pair
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
structure IsPair_k (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ) : Prop where
  base : GoodK σ B
  herm : X.IsHerm σ B r s
  skew : W.IsSkew σ B r' s'
  good : M.IsGood B.ψ
  hX : IsHecke F E χX
  hW : IsHecke F E χW
  resX : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n
  resW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d
  weil : M.IsWeil B.ψ χX χW om
end Pair
variable {a a' : ℕ}
def ThetaBasic_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair_k B M χX χW om
      r s r' s' →
    (∀ Φ ∈ schA F _, Continuous (fun x : UA σ X.J × UA σ W.J => theta om Φ x.1 x.2) ∧
      (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) ∧
      ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ g h, Continuous fun f : SInf F (Fin n × Fin d) => theta om (pureA F f φ) g h
def StabEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (X : Spc F E n) (r s : ℕ), GoodK σ B → X.IsHerm σ B r s →
    ∃ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K ∧ IsCompact (K : Set (UA σ X.J)) ∧
      μK.IsHaarMeasure ∧ μ.IsHaarMeasure
def ActsEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair_k B M χX χW om
      r s r' s' → ∀ v : Pl F,
    (∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁) ∧
    (∀ u, At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∀ x ∈ U, x.1 ∈ UAt σ X (evFin F v) →
      x.2 ∈ UAt σ W (evFin F v) → Acts (evFin F v) (om x) φ φ
end GlobalTheory.ThK
end

noncomputable section
namespace Tw.VacAny
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain
  NumberField MeasureTheory Matrix Classical _root_.GlobalTheory _root_.GlobalTheory.VacAny

theorem exists_isVac_any_darboux_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ
  : E →ₐ[F] E}
    (B : Base F E), GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R :=
      AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co v
  obtain ⟨θ, hθ⟩ := _root_.Tw.exists_int_add_conj_eq_one_of_base_good_k B hB
  obtain ⟨M, _, g, hΓ⟩ := Tw.LatParam.latAtV_param X Y hX.lat.toIsLattice hY.lat.toIsLattice v
  let γf : (M → v.adicCompletionIntegers F) → Matrix (Fin n) (Fin d)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    fun a => ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) •
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)
  let u : M → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun m =>
    (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g
      m))).1 i),
     fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g
       m))).2 i))
  let χ : (M → v.adicCompletionIntegers F) → ℂ := fun a => B.ψ (⅟(2 : AF F) *
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F :=
      F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γf a) (γf a))
  have he : ∀ a, co.e (γf a) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • co.e
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a

    simp only [γf, map_sum, map_smul]
  have hcomp : ∀ a i, (co.e (γf a)).1 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i ∧
      (co.e (γf a)).2 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i := by
    intro a i
    rw [he]
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, smul_eq_mul]
  have hAt : ∀ a i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e
    (γf a)).1 i) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).2 i)
        := by
    intro a i
    rw [(hcomp a i).1, (hcomp a i).2]
    exact ⟨GlobalTheory.VacAny.at_sum _ fun m _ => GlobalTheory.VacAny.at_mul_right (GlobalTheory.VacAny.at_atPlace _) _,
      GlobalTheory.VacAny.at_sum _ fun m _ => GlobalTheory.VacAny.at_mul_right (GlobalTheory.VacAny.at_atPlace _) _⟩
  have hev : ∀ a, ((fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i)),
      (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i))) = ∑ m, (a m : Fv F v) • u m := by
    intro a
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)

    · simp [(hcomp a i).1, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Finset.sum_apply, u]

    · simp [(hcomp a i).2, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.snd_sum, Finset.sum_apply, u]
  have hψ : ∀ z : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      B.ψ z = GlobalTheory.VacAny.psiV B.ψ v (GlobalTheory.AdelicU.evFin F v z) := fun z hz => by
    rw [GlobalTheory.VacAny.psiV_apply, ← eq_atPlace_of_at v z hz]
  have hzero : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → γf a = 0 := by
    intro a h
    rw [← hev a] at h
    have h1 : co.e (γf a) = 0 := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [eq_atPlace_of_at v _ (hAt a i).1, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i) = 0 from
          congrFun (congrArg Prod.fst h) i, map_zero]
        rfl
      · rw [eq_atPlace_of_at v _ (hAt a i).2, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i) = 0 from
          congrFun (congrArg Prod.snd h) i, map_zero]
        rfl
    exact co.e.map_eq_zero_iff.1 h1
  have hker : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1 := by
    intro a h
    simp only [χ, hzero a h]
    simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hadd : ∀ a b, γf (a + b) = γf a + γf b := by
    intro a b
    simp only [γf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (((a + b) m : v.adicCompletionIntegers F) : Fv F v) = (a m : Fv F v) + b m from rfl, map_add (f := _),
      add_smul]
  have hmem : ∀ a, γf a ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := fun a => (hΓ _).2 ⟨a,
    rfl⟩
  have hdot : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e
    (γf a)).1 ⬝ᵥ (co.e (γf b)).2) ∧
      GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) =
        (∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 := by
    intro a b
    refine ⟨GlobalTheory.VacAny.at_sum _ fun i _ => GlobalTheory.VacAny.at_mul_right (hAt a i).1 _, ?_⟩
    rw [← hev a, ← hev b]

    simp only [dotProduct, map_sum, map_mul]
  have hcoc : ∀ a b, χ (a + b) = χ a * χ b * GlobalTheory.VacAny.psiV B.ψ v
      (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
        (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2))) := by
    intro a b
    simp only [χ]
    rw [hadd, _root_.Tw.VacCocycle.psi_half_symp_add_k B hB X Y r s r' s' hX hY θ hθ v _ (hmem a) _ (hmem b), co.form]
    congr 1
    have hz := GlobalTheory.VacAny.at_neg (GlobalTheory.VacAny.at_mul_left (⅟(2 : AF F))
      (GlobalTheory.VacAny.at_sub (hdot a b).1 (hdot b a).1))
    rw [hψ _ hz, map_neg, map_mul, map_sub, (hdot a b).2, (hdot b a).2, GlobalTheory.VacAny.evFin_invOf_two]
  obtain ⟨φ, hφSB, hφ0, hφ⟩ := GlobalTheory.VacLoc.exists_schr_eigen v (GlobalTheory.VacAny.psiV B.ψ v)
    (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (Tw.PsiNontriv.psiV_ne_one B.ψ hB.std v) u χ (Tw.ContSymp.continuous_psi_symp_atPlace σ B.ψ hB.std.1 X.J Y.J (θ : E)
      v g) hker hcoc
  refine ⟨φ, hφSB, hφ0, θ, hθ, ?_⟩
  intro γ hγ
  obtain ⟨a, rfl⟩ := (hΓ γ).1 hγ
  intro rr hrr
  show GlobalTheory.WeilM.schr B.ψ (co.e (γf a)) _ = _
  rw [Tw.SchrLoc.schr_tens_of_at B.ψ v (co.e (γf a)) (fun i => (hAt a i).1) (fun i => (hAt a i).2) φ rr hrr.1, hev a,
    hφ a]
end Tw.VacAny
end

noncomputable section
namespace PositivityTheory.ThKF0.Grow
open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.LFun GlobalTheory.ThK in
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
theorem schwartz_decay_uniform (hA : HtBd) (hF : FinInv) (hS : Sob) (hT : TrBd) : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X :
  Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
  GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ),
  ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  obtain ⟨C, -, hC⟩ := hA F E σ n d X W M
  obtain ⟨C', k, -, h⟩ := weighted hF hS hT hP.base.std hΦ N
  refine ⟨C' * C ^ k, k, fun g g' x => ?_⟩
  obtain ⟨m, h1, h2, h3⟩ := hC g g'
  rw [mul_assoc, ← mul_pow]
  exact h _ _ m _ h1 h2 (impl_sOf hP.weil g g') h3 x
end PositivityTheory.ThKF0.Grow
end

noncomputable section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem schA_facts_k {B : Base F E} {σ : E →ₐ[F] E} (hB : GoodK σ B) (N : ℕ) (μN : Measure (Fin
  N → AF F))
    (hμN : μN.IsAddHaarMeasure) (Φ : (Fin N → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin N)) :
    Continuous Φ ∧ Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μN ∧
      ∀ b : Fin N → AF F, (fun x => B.ψ (x ⬝ᵥ b) * Φ x) ∈ schA F (Fin N) := by
  refine ⟨GlobalTheory.ThKOp.continuous_of_mem_schA hΦ, ?_, fun b => ?_⟩
  · have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    have : BorelSpace (AF F) := ⟨rfl⟩
    have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
    have key : ∀ (m : MeasurableSpace (Fin N → AF F)), m = borel _ → ∀ μ : @Measure _ m,
        @Measure.IsAddHaarMeasure _ _ _ m μ → Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μ := by
      rintro m rfl μ hμ
      have hm := schA_memLp_two F (Fin N) μ hμ Φ hΦ
      have hi := (hm.integrable_norm_pow two_ne_zero).ofReal (𝕜 := ℂ)
      refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    exact key _ hb μN hμN
  · have h := GlobalTheory.WeylFour.SchrKeep.schr_mem_schA F B.ψ hB.std (Fin N) (0, b) Φ hΦ
    convert h using 1
    funext x
    simp [schr]
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end

namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def EpsOf_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (n : ℕ) (X : Spc F E n) (r s : ℕ),
    (X.IsHerm σ B r s ∨ X.IsSkew σ B r s) → EpsHerm σ X.J ∧ r + s = n ∧ ∀ fr : Frame σ X.J, fr.IsGood → fr.r ≤ min r s
def CoefEq_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s',
    GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F),
    μ.IsAddHaarMeasure → ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
    ∀ (g : UA σ X.J) (h : UA σ W.J) (z : Ten F E n d), coef F B.ψ μ (om (g, h) Φ₁) (om (g,
    h) Φ₂) (M.co.e z) = coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * z * (mat h⁻¹)ᵀ))
def CoefBd_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s',
    GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F),
    μ.IsAddHaarMeasure → ∀ φ₁ ∈ SB (Fin n × Fin d → Af F), ∀ φ₂ ∈ SB (Fin n × Fin d → Af F), ∀ N : ℕ,
    ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)),
    Continuous p ∧ IsCompact C ∧ ∀ (f₁ f₂ : SInf F (Fin n × Fin d)) (z : Ten F E n d),
    ‖coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (M.co.e z)‖ ≤ p f₁ * p f₂ * maj B.emb C N z
end PositivityTheory.ThKEst

namespace PositivityTheory.ThKEst
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem epsOf_of_k : EpsOf_k := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero
      (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩
end PositivityTheory.ThKEst
end

noncomputable section
namespace PositivityTheory.ThKG.Tow.Stab
open scoped TensorProduct Matrix Pointwise RestrictedProduct
open NumberField IsDedekindDomain Topology Filter GlobalTheory.WeilM GlobalTheory.AdelicU
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
attribute [local instance] ae_ring ae_t2 ae_smul
theorem exists_compact_mat_k {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : GoodK σ B) (hX :
  X.IsHerm σ B r s) :
    ∃ S : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact S ∧ ∀ k ∈ stabK (σ := σ) B X, mat k ∈ S := by
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  choose C hC h using fin_bound X hX.lat
  choose R hR using fun w => cartan_bound (hX.cartan w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  refine ⟨Set.univ.pi fun i => Set.univ.pi fun j => (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C i j,
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC i j), fun k hk i _ j _ => ?_⟩
  rw [eΦ (mat k i j)]
  refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ (h i j _ fun y hy => (hk.2 y hy).1)
  rw [mem_closedBall_zero_iff]
  refine hR w ((mat k).map (piInf (B.emb w))) ?_ (hk.1 w) i j
  rw [← Levi.iso_map_piInf (σ := σ) (fun τ z => Levi.piInf_cA hB.cm τ z)]
  have e : (mat k)ᵀ * incM F X.J * (mat k).map (cA σ) = incM F X.J := k.2
  rw [e]
  exact Matrix.ext fun i j => Levi.piInf_incl _ _
theorem isCompact_stabK_k {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : GoodK σ B) (hX :
  X.IsHerm σ B r s) :
    IsCompact ((stabK B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  obtain ⟨S, hS, h⟩ := exists_compact_mat_k hB hX
  have hc := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have hU : IsClosed ((UG (cA σ) (incM F X.J) : Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  exact isCompact_of_units _ hU _ (isClosed_stabK B X (isCompact_latHat X hX.lat.fg).isClosed) S hS
    fun k hk => ⟨h k hk, h _ (inv_mem hk)⟩
end PositivityTheory.ThKG.Tow.Stab

namespace PositivityTheory.ThKG.Tow
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem stabEx_k : GlobalTheory.ThK.StabEx_k := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hc := Stab.isCompact_stabK_k hB hX
  obtain ⟨μK, hμK⟩ := Stab.exists_haar_of_isCompact _ hc
  obtain ⟨μ, hμ⟩ := Stab.exists_haar_idele (F := F) (E := E)
  exact ⟨Stab.stabK B X, μK, μ, Stab.isStab_stabK B X, hc, hμK, hμ⟩
end PositivityTheory.ThKG.Tow
end

noncomputable section
namespace PositivityTheory.ThKG.Tow
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
def ModelEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∃ M : Model σ X W, M.IsGood B.ψ
def WeilEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om
def PairEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → (∃ M : Model σ X W, M.IsGood B.ψ) ∧
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
      ∀ M : Model σ X W, M.IsGood B.ψ → ∃ om, GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s'
theorem pairEx_of_k (h₁ : ModelEx_k) (h₂ : WeilEx_k) : PairEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  refine ⟨h₁ F E σ B hB n d X W r s r' s' hX hW, fun χX χW a b c e M hM => ?_⟩
  obtain ⟨om, hom⟩ := h₂ F E σ B hB n d X W r s r' s' hX hW M hM χX χW a b c e
  exact ⟨om, hB, hX, hW, hM, a, b, c, e, hom⟩
end PositivityTheory.ThKG.Tow
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField MeasureTheory Matrix
  Classical GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter
  Topology
namespace Tw.VacIndic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isVac_indicator_of_theta_k {σ : E →ₐ[F] E} (B : Base F E) (hB : GoodK σ B) {n d : ℕ} (X
  : Spc F E n)
    (Y : Spc F E d) (r s r' s' : ℕ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s')
    (co : Darboux (symp (R := AF F)
      (cA σ) (-1)
      (incM F X.J)
      (incM F Y.J)) (Fin n × Fin d))
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun k => algebraMap F (AF F) (y k),
        fun k => algebraMap F (AF F) (z k)))
    (hθ : ∃ θ : 𝓞 E, (θ : E) + σ θ = 1) :
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  classical
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨G, hG⟩ := exists_gen X.L Y.L hX.lat.toIsLattice hY.lat.toIsLattice
  choose yc zc hc using hrat
  have e1 := eventually_psiLoc_eq_one B.ψ hB.std.1
  have e2 := eventually_int (F := F) (1 / 2)
  have e3 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ k, algebraMap F (Fv F v) (yc g k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zc g k) ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => Filter.eventually_all.2 fun k => ?_
    exact (eventually_int (yc g k)).and (eventually_int (zc g k))
  have e4 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ g' ∈ G,
      algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J g g') ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => (Filter.eventually_all_finset G).2 fun g' _ => ?_
    exact eventually_int _
  filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
  set O := v.adicCompletionIntegers F
  set T : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
    {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ O ∧ ∃ g ∈ G, z = a • incM F g} with hT
  have hA : ∀ z ∈ AddSubgroup.closure T, ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) ∧
      evFin F v ((co.e z).1 k) ∈ O ∧ evFin F v ((co.e z).2 k) ∈ O := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
      intro k
      rw [map_smul, hc g]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right ha, at_mul_right ha, mul_mem hai (h3 g hg k).1, mul_mem hai (h3 g hg k).2⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨at_zero, at_zero, zero_mem _, zero_mem _⟩
    | add z z' _ _ h h' =>
      intro k
      simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨at_add (h k).1 (h' k).1, at_add (h k).2.1 (h' k).2.1, add_mem (h k).2.2.1 (h' k).2.2.1,
        add_mem (h k).2.2.2 (h' k).2.2.2⟩
    | neg z _ h =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨at_neg (h k).1, at_neg (h k).2.1, neg_mem (h k).2.2.1, neg_mem (h k).2.2.2⟩
  set S := symp (cA σ) (inclR (AF F) (θ : E)) (incM F X.J) (incM F Y.J) with hS
  have hB1 : ∀ z ∈ T, ∀ z' ∈ AddSubgroup.closure T, At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
    induction hz' using AddSubgroup.closure_induction with
    | mem z' hz' =>
      obtain ⟨a', ha', hai', g', hg', rfl⟩ := hz'
      rw [hS, symp_smul_incM, map_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right (at_mul_right ha), mul_mem (mul_mem hai hai') (h4 g hg g' hg')⟩
    | zero => rw [hS, symp_zero_right, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_right, map_add (f := _)]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_right, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  have hB2 : ∀ z ∈ AddSubgroup.closure T, ∀ z' ∈ AddSubgroup.closure T,
      At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact hB1 z hz z' hz'
    | zero => rw [hS, symp_zero_left, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_left, map_add (f := _)]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_left, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  refine ⟨indicator_int_mem_SB v, indicator_int_ne_zero v, θ, hθ, fun γ hγ => ?_⟩
  have hγ' := latAtV_le X Y G hG v hγ
  have hval : B.ψ (⅟(2 : AF F) * S γ γ) = 1 := by
    have hat := hB2 γ hγ' γ hγ'
    rw [psi_of_at B.ψ (at_mul_left hat.1)]
    refine h1 _ ?_
    rw [map_mul, invOf_two_eq, evFin_algebraMap]
    exact mul_mem h2 hat.2
  rw [← hS, hval, one_smul]
  exact acts_indicator co B.ψ v γ h1 h2 (fun k => (hA γ hγ' k).1) (fun k => (hA γ hγ' k).2.1)
    (fun k => (hA γ hγ' k).2.2.1) (fun k => (hA γ hγ' k).2.2.2)
end Tw.VacIndic
namespace Tw.VacIndic
theorem eventually_isVac_indicator_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
    (B : Base F E), GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : Darboux (symp (R := AF F)
      (cA σ) (-1)
      (incM F X.J)
      (incM F Y.J)) (Fin n × Fin d)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun k => algebraMap F (AF F) (y k),
      fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co hrat
  exact isVac_indicator_of_theta_k B hB X Y r s r' s' hX hY co hrat (_root_.Tw.exists_int_add_conj_eq_one_of_base_good_k
    B hB)
end Tw.VacIndic
end

noncomputable section
namespace PositivityTheory.ThKG.Tow
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem modelEx_k : ModelEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := _root_.Tw.RatDarboux.exists_rational_darboux_of_isGood_k B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1
    (by simpa using hX.herm) (det_herm hX)
  have hS := _root_.Tw.VacIndic.eventually_isVac_indicator_k B hB X W r s r' s' hX hW co hco
  have hA := _root_.Tw.VacAny.exists_isVac_any_darboux_k B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, ite_eq_left h]; exact h
    · simp only [vac, ite_eq_right h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact ite_eq_left hv
end PositivityTheory.ThKG.Tow
end
