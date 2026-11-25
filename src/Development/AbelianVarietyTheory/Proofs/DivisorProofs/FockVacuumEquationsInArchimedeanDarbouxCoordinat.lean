module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.VacBridge

section Coords

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infAd (x : mixedEmbedding.mixedSpace F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0)

def mulC (t : mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun x := fun i => t * x i
  map_add' x y := by funext i; simp [mul_add]
  map_smul' r x := by funext i; simp

def mulP (t : mixedEmbedding.mixedSpace F) :
    ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
  (mulC t).prodMap (mulC t)

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 * b.1) =
    InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * InfiniteAdeleRing.ringEquiv_mixedSpace F b.1
  rw [map_mul]

theorem evI_realAd (r : ℝ) : evI F (realAd F r) = algebraMap ℝ _ r := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ r)) = _
  exact RingEquiv.apply_symm_apply _ _

theorem mul_infAd (u : AF F) (x : mixedEmbedding.mixedSpace F) : u * infAd x = infAd (evI F u * x) := by
  refine Prod.ext ?_ ?_
  · show u.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 * x)
    rw [map_mul, RingEquiv.symm_apply_apply]
  · show u.2 * 0 = 0
    exact mul_zero _

theorem infAd_add (x y : mixedEmbedding.mixedSpace F) : infAd (x + y) = infAd x + infAd y := by
  refine Prod.ext ?_ ?_
  · exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x y
  · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) = 0 + 0
    rw [add_zero]

theorem infAd_zero : infAd (0 : mixedEmbedding.mixedSpace F) = 0 := by
  refine Prod.ext ?_ ?_
  · exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
  · rfl

theorem evI_infAd (x : mixedEmbedding.mixedSpace F) : evI F (infAd x) = x :=
  RingEquiv.apply_symm_apply _ _

theorem snd_eq_zero_of_at {a : AF F} (h : At (evI F) a) : a.2 = 0 := by
  have h0 : evI F ((0 : InfiniteAdeleRing F), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) = 0 := map_zero _
  have h1 := congrArg Prod.snd (h _ h0)
  change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * a.2 = 0 at h1
  rwa [one_mul] at h1

end Coords

section Dar

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
  {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}

def mkD (d : Darboux B κ) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) : W :=
  d.e.symm (fun i => infAd (y.1 i), fun i => infAd (y.2 i))

theorem mkD_mulP (d : Darboux B κ) (u : AF F)
    (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mkD d (mulP (evI F u) y) = u • mkD d y := by
  rw [mkD, mkD, ← LinearEquiv.map_smul]
  congr 1
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact (mul_infAd u (y.1 i)).symm
  · exact (mul_infAd u (y.2 i)).symm

theorem mkD_add (d : Darboux B κ) (y y' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mkD d (y + y') = mkD d y + mkD d y' := by
  rw [mkD, mkD, mkD, ← map_add (f := _)]
  congr 1
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact infAd_add (y.1 i) (y'.1 i)
  · exact infAd_add (y.2 i) (y'.2 i)

theorem mkD_smul_real (d : Darboux B κ) (r : ℝ)
    (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mkD d (r • y) = realAd F r • mkD d y := by
  rw [← mkD_mulP, evI_realAd]
  congr 1

theorem coord_mkD (d : Darboux B κ) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    coord d (mkD d y) = y := by
  simp only [coord, mkD, LinearEquiv.apply_symm_apply]
  exact Prod.ext (funext fun i => evI_infAd _) (funext fun i => evI_infAd _)

theorem at_mkD (d : Darboux B κ) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    At (evI F) (mkD d y) := by
  intro u hu
  rw [← mkD_mulP, hu]
  have h0 : mulP (0 : mixedEmbedding.mixedSpace F) y = 0 :=
    Prod.ext (funext fun i => zero_mul _) (funext fun i => zero_mul _)
  rw [h0, mkD, show ((fun i => infAd ((0 : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)).1 i),
    fun i => infAd ((0 : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)).2 i)) :
      (κ → AF F) × (κ → AF F)) = 0 from Prod.ext (funext fun i => infAd_zero) (funext fun i => infAd_zero), map_zero]

theorem mkD_coord (d : Darboux B κ) {w : W} (hw : At (evI F) w) : mkD d (coord d w) = w := by
  apply d.e.injective
  rw [mkD, LinearEquiv.apply_symm_apply]
  have h1 : ∀ i, At (evI F) ((d.e w).1 i) := fun i u hu => by
    have h := congrArg (fun z => (d.e z).1 i) (hw u hu)
    simpa only [LinearEquiv.map_smul, Prod.smul_fst, Pi.smul_apply, map_zero, Prod.fst_zero, Pi.zero_apply] using h
  have h2 : ∀ i, At (evI F) ((d.e w).2 i) := fun i u hu => by
    have h := congrArg (fun z => (d.e z).2 i) (hw u hu)
    simpa only [LinearEquiv.map_smul, Prod.smul_snd, Pi.smul_apply, map_zero, Prod.snd_zero, Pi.zero_apply] using h
  refine Prod.ext (funext fun i => Prod.ext ?_ ?_) (funext fun i => Prod.ext ?_ ?_)
  · exact RingEquiv.symm_apply_apply _ _
  · exact (snd_eq_zero_of_at (h1 i)).symm
  · exact RingEquiv.symm_apply_apply _ _
  · exact (snd_eq_zero_of_at (h2 i)).symm

end Dar

section Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {α β : Type}

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  show infEmb τ (compInf F E w (a ⊗ₜ[F] (1 : E))) = _
  simp only [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, infEmb_tmul, map_one, mul_one]
  rfl

theorem map_smul_piInf {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (M : Matrix α β (AE F E)) :
    (a • M).map (piInf τ) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) • M.map (piInf τ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul, piInf_algebraMap]

theorem ext_realAd [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((realAd F r).1 w) = (r : ℂ) := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  have h := congrArg (fun m : mixedEmbedding.mixedSpace F => m.1 ⟨w, hw⟩) (evI_realAd (F := F) r)
  simp only [evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  rw [h]
  simp

theorem at_of_matrix {u : Matrix α β (AE F E)} (h : At (evI F) u) (i : α) (j : β) : At (evI F) (u i j) :=
  fun t ht => by simpa using congrFun (congrFun (h t ht) i) j

theorem at_sub {u u' : Matrix α β (AE F E)} (h : At (evI F) u) (h' : At (evI F) u') : At (evI F) (u - u') :=
  fun t ht => by rw [smul_sub, h t ht, h' t ht, sub_zero]

variable (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
include hcm

theorem exists_at_map (M : InfinitePlace F → Matrix α β ℂ) :
    ∃ u : Matrix α β (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = M w := by
  choose z hz using fun (i : α) (j : β) => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ hcm τ (fun w => M w i j)
  refine ⟨Matrix.of z, fun t ht => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (hz i j).1 t ht
  · ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact (hz i j).2 w

theorem eq_of_at_map {u u' : Matrix α β (AE F E)} (h : At (evI F) u) (h' : At (evI F) u')
    (he : ∀ w, u.map (piInf (τ w)) = u'.map (piInf (τ w))) : u = u' := by
  rw [← sub_eq_zero]
  ext i j
  refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hcm τ _ (at_of_matrix (at_sub h h') i j) fun w => ?_
  have := congrFun (congrFun (he w) i) j
  simp only [Matrix.map_apply] at this
  rw [Matrix.sub_apply, map_sub, this, sub_self]

end Comp

section Frame

variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

theorem frame_inv (M : Matrix α α ℂ) (A : Matrix α ι ℂ) (J : Matrix ι ι ℂ) (hJ : J * J = 1)
    (h : Aᵀ * M * A.map star = J) (hr : ∃ A' : Matrix ι α ℂ, A * A' = 1) :
    ∃ A' : Matrix ι α ℂ, A' * A = 1 ∧ A * A' = 1 := by
  obtain ⟨R, hR⟩ := hr
  have h' : Aᵀ * M * A.map (starRingEnd ℂ) = J := h
  have e2 : J * Aᵀ * M * A.map (starRingEnd ℂ) = 1 := by
    simp only [Matrix.mul_assoc] at h' ⊢
    rw [h', hJ]
  have e1 : (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) = A := by ext i j; simp
  have hL : (J * Aᵀ * M).map (starRingEnd ℂ) * A = 1 := by
    have := congrArg (fun X : Matrix ι ι ℂ => X.map (starRingEnd ℂ)) e2
    rw [Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  refine ⟨R, ?_, hR⟩
  have : (J * Aᵀ * M).map (starRingEnd ℂ) = R := by
    calc _ = (J * Aᵀ * M).map (starRingEnd ℂ) * (A * R) := by rw [hR, Matrix.mul_one]
      _ = R := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
  rw [← this, hL]

end Frame

theorem jm_mul_self (P Q : ℕ) : Jm P Q * Jm P Q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

section Main

theorem exists_bridge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (AE F E)) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a b A C ε hcm hfr
  have := hcm.1
  obtain ⟨-, hA, hC⟩ := hfr
  choose IA hIA using fun w => frame_inv _ (A w) (Jm P Q) (jm_mul_self P Q) (hA w).1 (hA w).2
  choose IC hIC using fun w => frame_inv _ (C w) (Jm R S) (jm_mul_self R S) (hC w).1 (hC w).2
  have hback : ∀ w (X : Matrix α β ℂ), A w * (IA w * X * (IC w)ᵀ) * (C w)ᵀ = X := by
    intro w X
    have hCt : (IC w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hIC w).2, Matrix.transpose_one]
    calc _ = (A w * IA w) * X * ((IC w)ᵀ * (C w)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [(hIA w).2, hCt, Matrix.one_mul, Matrix.mul_one]
  let θA : InfinitePlace F → Matrix α α ℂ := fun w => A w * Jm P Q * IA w
  let θB : InfinitePlace F → Matrix β β ℂ := fun w => C w * Jm R S * IC w
  have hθA : ∀ w, θA w * θA w = 1 := fun w => by
    calc A w * Jm P Q * IA w * (A w * Jm P Q * IA w)
        = A w * Jm P Q * (IA w * A w) * Jm P Q * IA w := by simp only [Matrix.mul_assoc]
      _ = A w * (Jm P Q * Jm P Q) * IA w := by rw [(hIA w).1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [jm_mul_self, Matrix.mul_one, (hIA w).2]
  have hθB : ∀ w, θB w * θB w = 1 := fun w => by
    calc C w * Jm R S * IC w * (C w * Jm R S * IC w)
        = C w * Jm R S * (IC w * C w) * Jm R S * IC w := by simp only [Matrix.mul_assoc]
      _ = C w * (Jm R S * Jm R S) * IC w := by rw [(hIC w).1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [jm_mul_self, Matrix.mul_one, (hIC w).2]
  have hJmT : (Jm R S)ᵀ = Jm R S := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]
  have hθconj : ∀ w (X : Matrix α β ℂ),
      θA w * X * (θB w)ᵀ = A w * (Jm P Q * (IA w * X * (IC w)ᵀ) * Jm R S) * (C w)ᵀ := fun w X => by
    simp only [θA, θB, Matrix.transpose_mul, hJmT, Matrix.mul_assoc]
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ :=
    _root_.GlobalTheory.SignInvolDarboux.exists_bridge F E σ α β κ τ JA JB d θA θB (fun _ => 1) ε hcm hθA hθB
  refine ⟨J, e, e', hJ, he, hJe, he1, he2, fun y => ?_⟩
  obtain ⟨u, u', u₁, hu, hu', hu₁, hmu', hmu₁, hc, hc', hc₁⟩ := hy y
  refine ⟨u, u', u₁, fun w => IA w * u.map (piInf (τ w)) * (IC w)ᵀ, hu, hu', hu₁, fun w => (hback w _).symm,
    fun w => ?_, fun w => ?_, hc, hc', hc₁⟩
  · rw [hmu' w, hθconj w, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hmu₁ w, hθconj w, Units.val_one, Int.cast_one, one_mul, Matrix.mul_smul, Matrix.smul_mul]

end Main

end GlobalTheory.VacBridge
