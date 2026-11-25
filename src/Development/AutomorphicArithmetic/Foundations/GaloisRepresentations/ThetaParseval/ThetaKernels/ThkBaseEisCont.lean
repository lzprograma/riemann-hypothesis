module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowModel
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
public import Development.WeilBound.ThetaLifts.LatticeBasics.CompCA
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameB
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesX
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
public import Development.WeilBound.ThetaLifts.LatticeBasics.SWFull
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
public import Development.WeilBound.ThetaLifts.LatticeBasics.SkewTwo
public import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

/-! # ThkBaseEisCont: Consolidated global theta-kernel definitions and proofs (ThkBaseEisCont). -/
@[expose] public section

open UpperTheory.TP.W (GoodK)

noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.TP.W (GoodK)
open GlobalTheory.Doubling (absE)
def SWAniso_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n :
    ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s',
    GoodK σ B → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l,
      IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ
def EisContinues_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (Y : Spc F E n) r s, GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ b : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ b →
    ∀ K a, IsStab2 (σ := σ) (Y := Y) B K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ U Ê, IsEisCont (flat a f s₁) U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k
def SWAnisoX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s',
    GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) (((d : ℂ) - n) / 2)
        fun x => (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ
def SiegelWeilAniso_k : Prop := SWAniso_k ∧ SWAnisoX_k
def EisBL_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (Y : Spc F E n) r s, GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x,
          (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U
def FrameConj_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (Y : Spc F E n) r s, GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → ∃ b K₀ p t, IsFrame2 σ Y b ∧ IsStdK B b K₀ ∧ IsPar p t ∧ ∀ k,
      k ∈ K ↔ p⁻¹ * k * p ∈ K₀
end GlobalTheory.ThK.Dbl
end

section
namespace GlobalTheory
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField MeasureTheory Matrix Classical GlobalTheory.FunObj GlobalTheory.ChiGrid
  GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
theorem exists_int_add_conj_eq_one_of_base_good_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), GoodK σ B → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  exact Tw.exists_int_add_conj_eq_one_of_base_good_k
end GlobalTheory
end

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open UpperTheory.TP.W (GoodK)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y :
  Spc F E n}
structure Std_k (B : Base F E) {m : ℕ} (A : Spc F E m) (Y : Spc F E n) (r s r' s' : ℕ) (χ : Chr F E) (κ :
  Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ)
    (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)) (Φ : (κ → AF F) → ℂ) : Prop where
  good : GoodK σ B
  hm : 1 ≤ m
  hn : 1 ≤ n
  hnm : n < m
  aniso : min r s = 0
  sign : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s'
  hecke : IsHecke F E χ
  res : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m
  dbl : IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l
  frame : IsFrame2 σ Y b
  stdK : IsStdK B b K
  hgt : IsHgt K a
  haar : μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ A.J) D μ
  sch : Φ ∈ schA F κ
  fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ))
def SWStdLt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n :
    ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std_k (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ →
      EisValueAt (sec om l a m Φ) (s0 m n) (thetaMean om S μ D Φ)
end PositivityTheory.SiegelWeilFormula
end

noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open UpperTheory.TP.W (GoodK)
namespace GlobalTheory.KFinLoc
theorem split_or_inert_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F]
  E) (B : Base F E),
    GoodK σ B → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E),
      Formalism.UG.IsInertAt F E v w := by
  intro F E _ _ _ _ _ σ B hB v
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun w _ => ?_
    exact Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | hi
  · left
    obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨(GlobalTheory.AdelicU.existsUnique_splitPrime_eq hB.cm hne h1 h2).exists.choose⟩
  · exact Or.inr hi
end GlobalTheory.KFinLoc
end

noncomputable section
open UpperTheory.TP.W (GoodK)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def DblX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair_k B M χX χW om r s r' s' → ∃ dd om₂ S l,
      IsDbl (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ h g g' x, IsEmb g g' x →
        detInv χW g' * thetaSum F (om₂ x (S h (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g' h) ∧
        detInv χW g' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (g, 1) Φ₁) (star (om (g', 1) Φ₂))) ∧
      IsDblCoordX M dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν
def BoxSecX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s',
    GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M, IsSec K χ (((d : ℂ) - n) / 2) (fun x => l (om x (boxFun Φ₁ (star Φ₂))))
def SWFullX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s',
    GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê,
        IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) U Ê ∧ (((d : ℂ) - n) / 2) ∈ U ∧
        ∀ x, Ê (((d : ℂ) - n) / 2) x = (if n < d then 1 else 2) * ⨍ h in D,
          thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ
end GlobalTheory.ThK.Dbl

namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem dblX_k : DblX_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨hw, ⟨d', ht, hw'⟩, -⟩ := h.weil
  have ht' : ∀ x, M.co.e xᵀ = d'.e x := fun x => (ht xᵀ).symm
  obtain ⟨dd, om₂, S, h1, h2, h3⟩ := dbl_main h.base.std h.base.cm.2.2.1
    (by simp [mul_comm]) (skew_det h.skew) (herm_det h.herm)
    h.hX.1 (fun x => by rw [← ht']; exact h.good.rat xᵀ) ht' hw' hw
  refine ⟨dd, om₂, S, _, h1, fun φ hφ φ' hφ' => ⟨box_mem hφ hφ', fun k g g' x hx =>
    ⟨?_, (h3 φ hφ φ' hφ').2 g g' x hx⟩⟩, ⟨d', ht, h2⟩, lD_haar⟩
  have p := h.weil.isUSplitting.pres
  have e : ∀ (g : UA σ X.J) ϕ, om.comp (MonoidHom.inl _ _) g (om.comp (MonoidHom.inr _ _) k ϕ) = om (g,
    k) ϕ := fun g ϕ => by
    rw [← mul_apply_eq_comp, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]; simp
  rw [(h3 φ hφ φ' hφ').1, ← thetaSum_smul, (h3 _ (hw.1.pres k φ hφ) _ (hw.1.pres k φ' hφ')).2 g g' x hx, e, e,
    theta_box (p _ φ hφ) (p _ φ' hφ')]
  rfl
end GlobalTheory.ThK.Dbl
end

noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK PositivityTheory.ThK.Vac
  PositivityTheory.ThKH.Iwas GlobalTheory.Doubling PositivityTheory.ThKG.Loc.Cone.Vf
open Formalism.UG (bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v :
  Pl F}
theorem exists_res_k {B : Base F E} (hB : GoodK σ B) (v : Pl F) : ∃ (K : Type) (_ : Field K) (r
  : intLoc F E v →+* K),
    Function.Surjective r ∧ (((∀ z, r z = 0 → r (cInt σ v z) = 0) ∧ ∃ κ, r (κ - cInt σ v κ) ≠ 0) ∨
      ∃ η, r η = 1 ∧ r (cInt σ v η) = 0) ∧ ∀ z, r z ≠ 0 → r (cInt σ v z) ≠ 0 → IsUnit z := by
  have hσ := hB.cm
  rcases GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · let ρ : intLoc F E v →+* v.adicCompletionIntegers F := ((splitProj τ : Fv F v ⊗[F] E →+* Fv F v).comp
      (intLoc F E v).subtype).codRestrict (v.adicCompletionIntegers F).toSubring fun z => splitProj_mem τ z.2
    have mk : ∀ a b : v.adicCompletionIntegers F, (splitAlgEquiv hσ τ).symm (a.1, b.1) ∈ intLoc F E v := fun a b =>
      (mem_intLoc_iff_split hσ τ).2 ⟨by rw [splitProj_symm]; exact a.2, by rw [splitProj_comp_symm]; exact b.2⟩
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ,
      IsLocalRing.residue_surjective.comp fun a => ⟨⟨_, mk a 0⟩, Subtype.ext (splitProj_symm hσ τ _)⟩,
      .inr ⟨⟨_, splitIdem_mem hσ τ⟩, ?_, ?_⟩, fun z h1 h2 => ?_⟩
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext (splitProj_splitIdem hσ τ) : ρ ⟨_,
        splitIdem_mem hσ τ⟩ = 1)).trans (map_one _)
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext ((splitProj_comp τ σ _).symm.trans (splitProj_comp_splitIdem
        hσ τ)) :
        ρ (cInt σ v ⟨_, splitIdem_mem hσ τ⟩) = 0)).trans (map_zero _)
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨b, hb⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h2).exists_right_inv
      refine IsUnit.of_mul_eq_one ⟨_, mk a b⟩ (Subtype.ext (split_ext hσ τ ?_ ?_))
      · rw [Subring.coe_mul, map_mul, splitProj_symm, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
      · rw [Subring.coe_mul, map_mul, splitProj_comp_symm, Subring.coe_one, map_one, splitProj_comp];
          exact congrArg Subtype.val hb
  · have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
    obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
    obtain ⟨ϖ, -, hv, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hσ hw hc
    let ρ : intLoc F E v →+* w.adicCompletionIntegers E :=
      ((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z =>
        toCompl_mem hu z.2
    have sj : Function.Surjective ρ := fun a => by
      obtain ⟨z, hz⟩ := (toCompl_bijective hw hu).2 a.1
      exact ⟨⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ a.2)⟩, Subtype.ext hz⟩
    have un : ∀ z, ((IsLocalRing.residue _).comp ρ) z ≠ 0 ↔ Valued.v (toCompl hu z.1) = 1 := fun z =>
      (IsLocalRing.residue_ne_zero_iff_isUnit _).trans HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ, IsLocalRing.residue_surjective.comp sj,
      .inl ⟨fun z hz => by_contra fun h => (un z).2 ?_ hz, ?_⟩, fun z h1 _ => ?_⟩
    · rw [← hv, hc]
      exact (un (cInt σ v z)).1 h
    · obtain ⟨κ, hκ⟩ := sj ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩
      refine ⟨κ, (un _).2 ?_⟩
      change Valued.v (toCompl hu (κ.1 - sigR _ σ κ.1)) = 1
      rw [map_sub, ← hc, show toCompl hu κ.1 = x from congrArg Subtype.val hκ, Valuation.map_sub_swap, hx1]
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨z', rfl⟩ := sj a
      refine IsUnit.of_mul_eq_one z' (Subtype.ext ((toCompl_bijective hw hu).1 ?_))
      rw [Subring.coe_mul, map_mul, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
theorem exists_beta_k {B : Base F E} (hB : GoodK σ B) {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ
  B r s)
    (g : UG (cA σ) (dbl (incM F X.J))) {x y a₁ a₂ : Matrix (Fin n) (Fin n) (AE F E)}
    (hg : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows x y) (hx : x ∈ Pres v X) (hy : y ∈ Pres v
      X)
    (h1 : a₁ ∈ Pres v X) (h2 : a₂ ∈ Pres v X) (h : a₁ * x + a₂ * y = 1) (ax : At (evFin F v) (x - 1)) (ay : At (evFin F
      v) (y - 1)) :
    ∃ b b' t', Adj (cA σ) (incM F X.J) b b' ∧ b + b' = -1 ∧ b ∈ Pres v X ∧ t' ∈ Pres v X ∧ (y + b * (y - x)) * t' = 1 :=
      by
  have hσ := cm_conj_conj hB.cm
  have cc := _root_.GlobalTheory.ThK.Dbl.cA_cA hB.cm
  have hL := hX.lat
  obtain ⟨K, _, ρ, r1, r2, r3⟩ := exists_res_k hB v
  obtain ⟨P, p1, p2⟩ := Frames.exists_rational_frame X.L v
  obtain ⟨G', hG', g1, g2⟩ := Hgt.gram_loc (v := v) (herm_det hX) hL.fg (I := IsIntegral ℤ) (fun z hz b =>
    hz.mul b.2) hX.dual
    isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P p1 p2
  simp only [inv_one, one_mul] at g1 g2
  have ha := fr_iff (Frames.frame_of_rational P p1 p2)
  set G₀ := P.1ᵀ * X.J * P.1.map σ with hG₀
  let ι := inclR (F := F) (E := E) (Fv F v)
  set a : GL (Fin n) (Fv F v ⊗[F] E) := bc ι P
  let j := (intLoc F E v).subtype.mapMatrix (m := Fin n)
  have inj : Function.Injective j := fun A B e => Matrix.ext fun i k => Subtype.ext (congrFun₂ e i k)
  let G : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g1 i k).mem⟩
  let H : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g2 i k).mem⟩
  have eG : a.1ᵀ * (incM F X.J).map (compFin F E v) * a.1.map (sigR _ σ) = j G := by
    change _ = G₀.map ι
    rw [hG₀, Matrix.map_mul, Matrix.map_mul, show (incM F X.J).map (compFin F E v) = X.J.map ι from
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] X.J i k) (map_one (evFin F v))]
    rfl
  have jj : ∀ N N' : Matrix (Fin n) (Fin n) (intLoc F E v), j (Nᵀ * G * N'.map (cInt σ v)) = (j N)ᵀ * j G * (j N').map
    (sigR _ σ) :=
    fun N N' => by rw [map_mul, map_mul]; rfl
  obtain ⟨θ₀, hθ⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let θ : AE F E := inclR (F := F) (AF F) (θ₀ : E)
  have iθ : compFin F E v (-θ) ∈ intLoc F E v := by
    rw [map_neg]; exact neg_mem (tmul_mem_intLoc (show evFin F v 1 ∈ _ by rw [map_one]; exact one_mem _) θ₀)
  have b0 : Adj (cA σ) (incM F X.J) ((-θ) • 1) ((-cA σ θ) • 1) := Adj.one.smul (by rw [map_neg, cc])
  have hb0 : (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (-cA σ θ) • 1 = -1 := by
    rw [← add_smul, ← neg_add, show θ + cA σ θ = inclR (F := F) (AF F) (θ₀ + σ θ₀ : E) from (map_add _ _ _).symm, hθ,
      map_one,
      neg_smul, one_smul]
  have pb0 := smul_mem_Pres hL iθ (one_mem (Pres v X))
  have lag := lag_of b0 hb0 g hg
  set b₀ := (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E))
  have pm := sub_mem hy hx
  obtain ⟨Nm, hNm⟩ := (ha _).1 pm
  obtain ⟨NM, hNM⟩ := (ha _).1 (add_mem hy (mul_mem pb0 pm))
  obtain ⟨NP, hNP⟩ := (ha _).1 (add_mem h1 h2)
  obtain ⟨NQ, hNQ⟩ := (ha _).1 (sub_mem (neg_mem h1) (mul_mem (add_mem h1 h2) pb0))
  obtain ⟨S, s1, s2⟩ := exists_skew (c := cInt σ v) (r := ρ) (G := G) (G' := H) (M := NM) (m := Nm) (P := NP) (Q := NQ)
    (fun z => Subtype.ext (by
      change sigR _ σ (sigR _ σ z.1) = z.1
      induction z.1 using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
      | add x y hx hy => simp only [map_add (f := _), hx, hy])) r1
    (fun i k => Subtype.ext (congrArg ι (by
      change σ (G₀ k i) = G₀ i k

      simp only [hG₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hX.herm,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)))
    (inj (by
      rw [map_mul, map_one]
      change G₀.map ι * G'.map ι = 1
      rw [← Matrix.map_mul, mul_eq_one_comm.1 hG', Matrix.map_one _ (map_zero _) (map_one _)])) r2 r3
    (inj (by
      rw [map_add (f := _), jj, jj, hNm, hNM, ← eG, ← gram_fr, ← gram_fr, ← Matrix.add_mul, ← Matrix.mul_add,
        ← Matrix.map_add _ (map_add _), lag, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul,
          map_zero]))
    (inj (by
      rw [map_add (f := _), map_mul, map_mul, hNm, hNM, hNP, hNQ, ← map_mul, ← map_mul, ← map_add (f := _), map_one,
        ← map_one (fr v a), ← h]
      congr 1
      noncomm_ring))
  let SA : Matrix (Fin n) (Fin n) (AE F E) := (a.1 * j S * (a⁻¹).1).map (sgE E v)
  have aS : At (evFin F v) SA := fun u hu => Matrix.ext fun i k => at_sgE _ u hu
  have fS : fr v a SA = j S := by
    rw [fr_apply, show SA.map (compFin F E v) = a.1 * j S * (a⁻¹).1 from Matrix.ext fun _ _ => comp_sgE _]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  have sk : SAᵀ * incM F X.J + incM F X.J * SA.map (cA σ) = 0 := by
    have k1 := gram_fr (σ := σ) a (incM F X.J) SA 1
    have k2 := gram_fr (σ := σ) a (incM F X.J) 1 SA
    have k3 := congrArg j s1
    have k4 := jj S 1
    have k5 := jj 1 S
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, map_one, mapc_one, fS, eG,
      Matrix.map_one _ (map_zero (sigR (Fv F v) σ)) (map_one _), Matrix.map_one _ (map_zero (cInt σ v)) (map_one _)]
        at k1 k2 k4 k5
    rw [map_add (f := _), k4, k5, ← k1, ← k2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add _),
      map_zero] at k3
    have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
    have u2 : IsUnit (a.1.map (sigR (Fv F v) σ)) := a.isUnit.map (sigR (Fv F v) σ).mapMatrix
    rw [u2.mul_left_eq_zero, u1.mul_right_eq_zero] at k3
    refine Matrix.ext fun i k => eq_zero_of_at (v := v) (fun u hu => congrFun₂ (at_add (at_mul_left (M := SAᵀ)
      (fun u hu => congrArg Matrix.transpose (aS u hu)) _) (at_mul_right _ (N := SA.map (cA σ)) fun u hu =>
        Matrix.ext fun i k => by
        change u • cA σ (SA i k) = 0
        rw [← map_smul, show u • SA i k = 0 from congrFun₂ (aS u hu) i k, map_zero]) u hu) i k) (congrFun₂ k3 i k)
  have am : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  obtain ⟨t', pt, ht⟩ := exists_inv ha (f := y + (b₀ + SA) * (y - x)) (N := NM + S * Nm)
    (by rw [add_sub_right_comm]; exact at_add ay (at_mul_right _ am))
    (by rw [map_add (f := _), map_mul, hNm, hNM, ← fS, ← map_mul, ← map_add (f := _), add_mul, add_assoc]) s2
  exact ⟨b₀ + SA, _ + -SA, t', b0.add (by rw [Adj, mapc_neg, Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left sk),
    by rw [add_add_add_comm, add_neg_cancel, add_zero, hb0], add_mem pb0 ((ha _).2 ⟨S, fS.symm⟩), pt, ht⟩
end GlobalTheory.ThK.Dbl.Vf2
end

noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y :
  Spc F E n}
theorem eisContinues_of_k (h1 : EisBL_k) (h2 : FrameConj_k) : EisContinues_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc K a hK ha s₁ f hf
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r s hB hY K hK
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
  have hf₀ : IsSec K₀ χ s₁ fun x => f (x * p⁻¹) := by
    refine ⟨hf.cont.comp (continuous_mul_const _), fun q u x hq => by rw [mul_assoc, hf.law q u _ hq], ?_⟩
    have := hf.fin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1))).map
      (LinearMap.funLeft ℂ ℂ fun x => x * p⁻¹)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨_, hk' k k.2⟩, rfl⟩, funext fun x => by simp [LinearMap.funLeft, mul_assoc]⟩
  obtain ⟨Ê, ⟨t₁, e1, e2⟩, e3⟩ := h1 F E σ B n Y r s hB hn hY χ hχ c hc b K₀ _ hb hK₀ ha₀ s₁ _ hf₀
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (s₁ - z) :=
    (differentiable_id.const_sub s₁).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine (eisCont_of_reg (f := flat a f s₁) (Ê := fun z x => (d : ℂ) ^ (s₁ - z) * Ê z (x * p)) (t := t₁) (fun z hz x =>
    ?_)
    (fun x => dc.differentiableOn.mul (e2 _)) fun s₀ => ?_).imp fun U hU => ⟨_, hU⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mp ((e1 z hz (x * p)).mul_left ((d : ℂ) ^ (s₁ - z)))
    simp only [eisTerm, flat, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.ofReal_mul_cpow d0.le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · obtain ⟨k, U, H, hU, e4, e5⟩ := e3 s₀
    refine ⟨k, _,
      (reg_of_weak hU e5).mul one_le_height_GL2 (dc.analyticAt s₀) (continuous_mul_const p) (b := ht2 p) fun x => ?_,
      ?_⟩
    · rw [mul_comm]; exact_mod_cast heightGL_mul_le F x.1 p.1
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hz' x
      rw [e4 z hz hz', mul_left_comm]
end GlobalTheory.ThK.Dbl
end

noncomputable section
namespace GlobalTheory.ThK.Dbl.Frame
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.Doubling PositivityTheory.ThKH.Iwas Hgt
open UpperTheory.TP.W (GoodK)
open Formalism.UG (bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v :
  Pl F}
theorem inD_mem_k {B : Base F E} (hB : GoodK σ B) {w : Pl E} (hw : Formalism.UG.IsInertAt F E v
  w) {z : E} (hz : InD z) :
    inclR (F := F) (Fv F v) z ∈ intLoc F E v := by
  set Z := inclR (F := F) (Fv F v) z
  have key : ∀ y ∈ intLoc F E v, y * Z + sigR _ σ (y * Z) ∈ intLoc F E v := fun y hy => by
    refine intLoc_induction (p := fun y => y * Z + sigR _ σ (y * Z) ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun _ _ h h' => by convert add_mem h h' using 1; simp only [add_mul, map_add (f := _)]; ring)
      (fun _ h => by convert neg_mem h using 1; simp only [neg_mul, map_neg]; ring) hy
    convert tmul_mem_intLoc (mul_mem ha (trace_mem hB.std (hB.inert v w hw).2.2 (hz.mul x))) 1 using 1
    rw [show a ⊗ₜ[F] (x : E) * Z = a ⊗ₜ[F] (z * x) from (Algebra.TensorProduct.tmul_mul_tmul a 1 _ z).trans (by
      rw [mul_one, mul_comm])]
    change a ⊗ₜ[F] (z * x) + a ⊗ₜ[F] σ (z * x) = _
    rw [← TensorProduct.tmul_add, add_conj hB.cm, mul_comm a, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]
    rfl
  have hu := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
  obtain ⟨ϖ, -, -, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hB.cm hw hc
  obtain ⟨y, rfl⟩ := (toCompl_bijective hw hu).2 x
  have hy := (mem_intLoc_iff hw hu y).2 hx
  have h1 := (mem_intLoc_iff hw hu _).1 (sub_mem (mul_mem (sigR_mem_intLoc σ hy) (key 1 (one_mem _))) (key y hy))
  rw [show sigR _ σ y * (1 * Z + sigR _ σ (1 * Z)) - (y * Z + sigR _ σ (y * Z)) = (sigR _ σ y - y) * Z by
    simp only [one_mul, map_mul]; ring, map_mul, map_sub, ← hc] at h1
  refine (mem_intLoc_iff hw hu _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
  rwa [map_mul, hx1, one_mul] at h2
theorem exists_loc_k {B : Base F E} (hB : GoodK σ B) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ
  B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (v : Pl F) : ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)) (l : (Fv F v ⊗[F] E)ˣ),
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := by
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  have hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  let ι := inclR (F := F) (E := E) (Fv F v)
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  have eG : (bc ι P).1ᵀ * Y.J.map ι * (bc ι P).1.map (sigR _ σ) = G.map ι := by
    rw [hG, Matrix.map_mul, Matrix.map_mul]; rfl
  have one : ∀ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 → G'.map ι * G.map ι = 1 := fun G' h => by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  suffices h : ∃ l : (Fv F v ⊗[F] E)ˣ, Int (intLoc F E v) (((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι) ∧
      ∃ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 ∧ Int (intLoc F E v) ((l.1 * sigR _ σ l.1) • G'.map ι) by
    obtain ⟨l, a1, G', a2, a3⟩ := h
    have e : (l⁻¹ • bc ι P).1ᵀ * Y.J.map ι * (l⁻¹ • bc ι P).1.map (sigR _ σ) = ((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι :=
      by
      rw [← eG, mul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul]
      congr 1
      exact Matrix.ext fun i j => map_mul (sigR (Fv F v) σ) (l⁻¹).1 _
    refine ⟨bc ι P, l⁻¹ • bc ι P, l, Frames.frame_of_rational P h1 h2, (smul_inv_smul l _).symm, e ▸ a1, _, a3, ?_⟩
    rw [e, Matrix.smul_mul, Matrix.mul_smul, one G' a2, smul_smul, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one,
      one_mul, one_smul]
  rcases hY with h | h
  · obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
      isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2
    exact ⟨1, fun i j => by simpa using (b1 i j).mem, G', b0, fun i j => by simpa using (b2 i j).mem⟩
  obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
  obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2
  rw [← hG] at b0 b1
  rcases GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · have s1 : (G.map σ)ᵀ = -G := (gram_sym (σ : E →+* E) hσ (ε := -1)
      (Matrix.ext fun i j => (h.skew i j).trans (neg_one_mul _).symm) P.1).trans (neg_one_smul _ _)
    have s2 : (G'.map σ)ᵀ = -G' := by
      have e : (G.map σ)ᵀ * (G'.map σ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul]
        change (G'.map (σ : E →+* E) * G.map (σ : E →+* E))ᵀ = 1
        rw [← Matrix.map_mul, b0, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
      rw [← Matrix.one_mul (G'.map σ)ᵀ, ← b0, Matrix.mul_assoc, ← neg_neg G, ← s1, Matrix.neg_mul, e]; simp
    let u := (splitAlgEquiv hc τ).symm
    have fin : ∀ (d : E) (X : Matrix (Fin n) (Fin n) E), (X.map σ)ᵀ = -X → (∀ i j, LocInt v (d * X i j)) →
        Int (intLoc F E v) ((u (τ d, 1) * sigR _ σ (u (τ d, 1))) • X.map ι) := fun d X hX hd i j => by
      have q : ∀ i j, τ d * τ (X i j) ∈ v.adicCompletionIntegers F := fun i j => by
        simpa [inclR] using splitProj_mem τ (hd i j).mem
      have q' : σ (X i j) = -X j i := congrFun (congrFun hX j) i
      refine (mem_intLoc_iff_split hc τ).2 ⟨?_, ?_⟩
      · simpa [u, ι, inclR, ← splitProj_comp] using q i j
      · simpa [u, ι, inclR, splitProj_comp_sigR hc, q'] using q j i
    have e : u (τ δ, 1) * u (τ δ⁻¹, 1) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, ← map_mul, mul_inv_cancel₀ d0, map_one, mul_one]; exact map_one u
    exact ⟨⟨_, _, e, (mul_comm _ _).trans e⟩, fin _ _ s1 b1, G', b0, fin _ _ s2 b2⟩
  · have i1 := inD_mem_k hB hw d1
    have i2 := (d2 1 ((inD_iff _).2 (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))).mem
    refine ⟨1, fun i j => ?_, G', b0, fun i j => ?_⟩
    · simpa [← map_mul, d0] using mul_mem i1 (b1 i j).mem
    · simpa [← map_mul, d0] using mul_mem i2 (b2 i j).mem
theorem exists_ad_k {B : Base F E} (hB : GoodK σ B) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B
  r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (c : InfinitePlace F → GL (Fin n) ℂ) : ∃ a g : GL (Fin n) (AE F E), IsLatticeFrame Y.L a ∧
      (∀ v, (∃ l : (Fv F v ⊗[F] E)ˣ,
        (bc (compFin F E v) a).1 = l.1 • (bc (compFin F E v) g).1) ∧ Uni σ v Y.J (bc (compFin F E v) g)) ∧
      ∀ w, bc (piInf (B.emb w)) g = c w := by
  classical
  have hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨S, hS⟩ := Frames.exists_finset_latLoc_eq (F := F) Y.L
  have h0 : ∀ᶠ v : Pl F in cofinite, v ∉ S ∧ ∀ i j, LocInt v (Y.J i j) ∧ LocInt v (Y.J⁻¹ i j) :=
    S.eventually_cofinite_notMem.and (eventually_all.2 fun i => eventually_all.2 fun j => (ae_locInt _).and (ae_locInt
      _))
  have key : ∀ v : Pl F, ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)),
    (v ∉ Set.Finite.toFinset h0 → a = 1 ∧ g = 1) ∧ ∃ l : (Fv F v ⊗[F] E)ˣ,
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := fun v => by
    by_cases hv : v ∈ Set.Finite.toFinset h0
    · obtain ⟨a, g, h⟩ := exists_loc_k hB hY hJ v
      exact ⟨a, g, fun h => absurd hv h, h⟩
    · have hv' := not_not.1 (mt (Set.Finite.mem_toFinset h0).2 hv)
      refine ⟨1, 1, fun _ => ⟨rfl, rfl⟩, 1, fun y => by simpa using hS v hv'.1 y, (one_smul _ _).symm, ?_⟩
      rw [Uni, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one]
      refine ⟨fun i j => (hv'.2 i j).1.mem, Y.J⁻¹.map (inclR (Fv F v)), fun i j => (hv'.2 i j).2.mem, ?_⟩
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  choose a g h1 l h2 h3 h4 using key
  let e := fun w => RingEquiv.ofBijective _ (infEmb_bijective hB.cm (B.emb w))
  obtain ⟨a', ha, -⟩ := Frames.exists_GL_of_components _ a (fun v hv => (h1 v hv).1) fun _ => 1
  obtain ⟨g', hg,
    hg'⟩ := Frames.exists_GL_of_components _ g (fun v hv => (h1 v hv).2) fun w => bc (e w).symm.toRingHom (c w)
  refine ⟨a', g', fun v y => ha v ▸ h2 v y, fun v => ?_, fun w => Units.ext (Matrix.ext fun i j => ?_)⟩
  · rw [ha, hg]; exact ⟨⟨_, h3 v⟩, h4 v⟩
  · exact (congrArg (fun x => e w (x.1 i j)) (hg' w)).trans ((e w).apply_symm_apply _)
end GlobalTheory.ThK.Dbl.Frame
end

noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
theorem swFullX_of_k (h1 : SWAnisoX_k) (h2 : EisContinues_k) (h3 : BoxSecX_k) : SWFullX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂
    p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n X r s hB hn (.inl hX) χ hχ d hr K a hK ha _ _
    (h3 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((d : ℂ) - n) / 2)
  exact ⟨_, _,
    hE.update hk (h1 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1
    Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩
end GlobalTheory.ThK.Dbl
end

noncomputable section
open UpperTheory.TP.W (GoodK)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def HgtEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (Y : Spc F E n) r s, GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h'))
def Unfold0_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (Y : Spc F E n) r s, GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∀ (χ : Chr F E) (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsHecke F E χ → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ (f Ê : G2 σ Y → ℂ) (z : ℂ), Continuous f → Continuous Ê → (∀ x, HasSum (eisTerm f x) (Ê x)) →
      (∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x) →
    ∀ (μ : Measure (UA σ Y.J)) (D : Set (UA σ Y.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ Y.J) D μ →
      Integrable (fun g => f (e (1, g))) μ → ∀ φ : UA σ Y.J → ℂ, IsRapid φ → ∀ h,
        ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ
def HgtInt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (Y : Spc F E n) r s, GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K a (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → IsHgt K a → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ μ : Measure (UA σ Y.J), μ.IsHaarMeasure → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ
end GlobalTheory.ThK.Dbl

namespace GlobalTheory.ThK.Dbl
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {n : ℕ} {Y : Spc F E n}
def StdEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ)
    (Y : Spc F E n) r s, GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x
theorem stdEx_of_k (h1 : FrameConj_k) (h2 : HgtEx_k) : StdEx_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY
  obtain ⟨⟨K, a, hK, ha, hc, hp⟩, -⟩ := h2 F E σ B n Y r s hB hY
  obtain ⟨b, K₀, p, t, hb, hK₀, hpt, e⟩ := h1 F E σ B n Y r s hB hY K hK
  have h0 : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det t) := by
    rw [← ha.val p t hpt 1 K.one_mem]
    exact hp _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  refine ⟨b, K₀, fun x => absE F E (Matrix.GeneralLinearGroup.det t) * a (x * p⁻¹), hb, hK₀, ⟨fun x => ?_,
    fun q u hq k hk => ?_⟩,
    continuous_const.mul (hc.comp (continuous_mul_const _)), fun x => mul_pos h0 (hp _)⟩
  · obtain ⟨q, u, hq, k, hk, ex⟩ := ha.iwa (x * p⁻¹)
    exact ⟨q * p, u * t, hq.mul hpt, _, (e k).1 hk, by rw [mul_inv_eq_iff_eq_mul.1 ex]; group⟩
  · have := ha.val _ _ (hq.mul hpt.inv) (p * k * p⁻¹) ((e _).2 (by convert hk using 1; group))
    rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, this, ← NNReal.coe_mul, ← map_mul, mul_comm, ← map_mul,
      inv_mul_cancel_right]
end GlobalTheory.ThK.Dbl
end

noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.Doubling GlobalTheory.ThK.Dbl.Frame
open Formalism.UG (bc)
theorem frameConj_k : FrameConj_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  have hL : Y.L.IsLattice E := hY.elim (·.lat.toIsLattice) (·.lat.toIsLattice)
  have hJ := Frame.det_ne hY
  obtain ⟨ε, hε, c, c1, c2⟩ : ∃ ε : ℤˣ, (Y.J.map σ)ᵀ = ((ε : ℤ) : E) • Y.J ∧ ∃ c : ℂ, star c * c = 1 ∧
      ∀ w, (c • Y.J.map (B.emb w).1)ᴴ = c • Y.J.map (B.emb w).1 ∧ IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) := by
    rcases hY with h | h
    · refine ⟨1, Matrix.ext fun i j => by simpa using h.herm i j, 1, by simp, fun w => ?_⟩
      rw [one_smul]
      exact ⟨Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j)), h.cartan w⟩
    · refine ⟨-1, Matrix.ext fun i j => by simpa using h.skew i j, Complex.I, by simp,
        fun w => ⟨Matrix.ext fun i j => ?_, h.cartan w⟩⟩
      change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
      rw [star_mul', ← hc.2.2.2, h.skew]; simp
  have ee : ∀ (S : Type) [CommRing S], ((ε : ℤ) : S) * (ε : ℤ) = 1 := fun S _ => by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  choose gw hw using fun w => Frame.exists_arch c1 (c2 w).1 (Frame.isUnit_of_cartan (c2 w).2) (c2 w).2
  obtain ⟨a, g, ha, hg, hg'⟩ := Frame.exists_ad_k hB hY hJ gw
  obtain ⟨t, ht⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let ι := inclR (F := F) (E := E) (AF F)
  let cc : AE F E →+* AE F E := cA σ
  have hι : ∀ z, ι (σ z) = cc (ι z) := fun z => rfl
  have hcc : ∀ z, cc (cc z) = z := fun z => by
    change cA σ (cA σ z) = z
    rw [cA_eq]; exact sigR_invol hσ z
  have hf : ∀ v z, compFin F E v (cc z) = sigR _ σ (compFin F E v z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hi : ∀ w z, piInf (B.emb w) (cc z) = star (piInf (B.emb w) z) := fun w z => by
    refine Eq.trans (congrArg (infEmb (B.emb w)) ?_) (infEmb_sigR hc (B.emb w) (compInf F E w z)).symm
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have jf : ∀ v, (incM F Y.J).map (compFin F E v) = Y.J.map (inclR (F := F) (Fv F v)) := fun v =>
    Matrix.ext fun i j => congrArg (· ⊗ₜ[F] Y.J i j) (map_one (evFin F v))
  have ii : ∀ w z, piInf (B.emb w) (ι z) = (B.emb w).1 z := fun w z => by
    change InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 z = _
    rw [map_one, one_mul]
  have ji : ∀ w, (incM F Y.J).map (piInf (B.emb w)) = Y.J.map (B.emb w).1 := fun w => Matrix.ext fun i j => ii w _
  have h2 : (2⁻¹ : E) + σ 2⁻¹ = 1 := by rw [map_inv₀, map_ofNat]; norm_num
  let α : AE F E := ι 2⁻¹ + eF F • ι (t - 2⁻¹)
  have α0 : α + cc α = 1 := by
    have : cc α = ι (σ 2⁻¹) + eF F • ι (σ (t - 2⁻¹)) := by
      rw [hι, hι, map_add (f := _)]; exact congrArg _ (map_smul (cA σ) _ _)
    rw [this, add_add_add_comm, ← smul_add, ← map_add (f := _), ← map_add (f := _), h2, map_sub σ, sub_add_sub_comm, ht,
      h2, sub_self]
    simp
  have α1 : ∀ v, compFin F E v α ∈ intLoc F E v := fun v => by
    rw [map_add (f := _), comp_eF, ← map_add (f := _), ← map_add (f := _), add_sub_cancel]
    exact tmul_mem_intLoc (a := evFin F v 1) (by rw [map_one]; exact one_mem _) t
  have α2 : ∀ w, piInf (B.emb w) α = 2⁻¹ := fun w => by
    have : piInf (B.emb w) (algebraMap (AF F) (AE F E) (eF F)) = 0 := by
      change InfinitePlace.Completion.extensionEmbedding w 0 * (B.emb w).1 1 = _
      rw [map_zero, zero_mul]
    rw [map_add (f := _), Algebra.smul_def, map_mul, this, zero_mul, add_zero, ii, map_inv₀, map_ofNat]
  have uJ : IsUnit Y.J := (Matrix.isUnit_iff_isUnit_det _).2 hJ.isUnit
  obtain ⟨T₀, hT₀⟩ := exists_dual (σ : E →+* E) hσ uJ 1
  obtain ⟨T, hT⟩ := exists_dual cc hcc (J := incM F Y.J) (uJ.map ι.mapMatrix) g
  have g0 := frame_gram (σ : E →+* E) hσ (ee E) h2 hε 1 T₀ hT₀
  have g1 := frame_gram cc hcc (ee _) α0 (J := incM F Y.J) (Matrix.ext fun i j => by
    have := congrArg ι (congrFun (congrFun hε i) j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_intCast] at this
    exact this) g T hT
  have d0 := frame_diag 1 T₀ (2⁻¹ : E)
  set b := two 1 * wit (2⁻¹ : E) T₀
  have d1 := frame_diag g T α
  set b' := two g * wit α T with hb'
  have g2 : (bc ι b).1ᵀ * dbl (incM F Y.J) * (bc ι b).1.map cc = b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc := by
    have := (map_gram ι hι b.1 (dbl Y.J)).symm.trans (congrArg (·.map ι) g0)
    rw [map_dbl] at this
    rw [g1]
    refine this.trans ?_
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite ι]
  let p : G2 σ Y := ⟨b' * (bc ι b)⁻¹, by
    change (b'.1 * ((bc ι b)⁻¹).1)ᵀ * _ * (b'.1 * ((bc ι b)⁻¹).1).map cc = _
    calc _ = ((bc ι b)⁻¹).1ᵀ * (b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc) * ((bc ι b)⁻¹).1.map cc := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = ((bc ι b).1 * ((bc ι b)⁻¹).1)ᵀ * dbl (incM F Y.J) * ((bc ι b).1 * ((bc ι b)⁻¹).1).map cc := by
          simp only [← g2, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = _ :=
            by rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
            Matrix.mul_one]⟩
  have fr : ∀ k : G2 σ Y, inFrame b k = (b'⁻¹ * (p * k * p⁻¹).1 * b').1 := fun k => by
    rw [show b'⁻¹ * (p * k * p⁻¹).1 * b' = bc ι b⁻¹ * k.1 * bc ι b by
      change b'⁻¹ * (b' * (bc ι b)⁻¹ * k.1 * (b' * (bc ι b)⁻¹)⁻¹) * b' = _
      simp only [mul_inv_rev, inv_inv, map_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]]
    rfl
  have fin : ∀ k : G2 σ Y, Keeps (p * k * p⁻¹) ↔ ∀ i j, eF F • inFrame b k i j ∈ intHat F E := fun k => by
    simp only [keeps_iff hL.fg ha, mem_intHat, fr]
    refine (forall_congr' fun v => ?_).trans (forall_comm.trans (forall_congr' fun i => forall_comm))
    obtain ⟨⟨l, hl⟩, u1, G', u2, u3⟩ := hg v
    obtain ⟨q1, q2⟩ := int_dual (T := bc (compFin F E v) T) (sigR_invol hσ) (fun z => sigR_mem_intLoc σ) u1 u2 u3 (by
      have := congrArg (·.map (compFin F E v)) hT
      simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hf v), jf, Matrix.map_one _ (map_zero _) (map_one _)]
        at this
      rw [← this]
      congr 1
      exact Matrix.ext fun i j => (hf v _).symm)
    obtain ⟨q3, q4⟩ := int_wit (α1 v) q1 q2
    have := int_conj hl q3 q4 (bc (compFin F E v) (p * k * p⁻¹).1)
    simp only [← bc_wit, ← bc_two, ← map_mul (bc (compFin F E v)), ← map_inv (bc (compFin F E v))] at this
    exact this
  refine ⟨b, K.comap (MulAut.conj p).toMonoidHom, p, g, ⟨⟨ε, g0⟩, 1, ?_⟩, fun k => ?_, ?_, fun k => ?_⟩
  · rw [← d0, ← Matrix.fromCols_toCols b.1, Matrix.fromCols_mul_fromRows]; simp
  · refine (hK (p * k * p⁻¹)).trans (and_congr (forall_congr' fun w => ?_) ?_)
    · have := hw w (bc (piInf (B.emb w)) T) (by
        have := congrArg (·.map (piInf (B.emb w))) hT
        simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hi w), ji, Matrix.map_one _ (map_zero _) (map_one _)]
          at this
        rw [← this, ← hg']
        congr 1
        exact Matrix.ext fun i j => (hi w _).symm) (bc (piInf (B.emb w)) (p * k * p⁻¹).1) (by
        have := (map_gram _ (hi w) _ _).symm.trans (congrArg (·.map (piInf (B.emb w))) (show _ = _ from (p * k *
          p⁻¹).2))
        simp only [map_dbl, ji] at this
        exact this)
      rw [← hg', ← α2 w, ← bc_wit, ← bc_two, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at this
      rw [fr]
      exact this.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_and]
      refine Iff.trans ?_ (and_congr (fin k) (fin k⁻¹))
      rw [show p * k⁻¹ * p⁻¹ = (p * k * p⁻¹)⁻¹ by simp [mul_assoc]]
      simp only [Keeps, forall_and]
      exact and_and_and_comm
  · exact par_of ι (d0.trans (Matrix.mul_one _)) d1
  · change _ ↔ p * (p⁻¹ * k * p) * p⁻¹ ∈ K
    rw [show p * (p⁻¹ * k * p) * p⁻¹ = k by simp [mul_assoc]]
end GlobalTheory.ThK.Dbl
end
