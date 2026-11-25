module

import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatLin
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FiniteFamilyOfCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.HM

variable {F : Type} [Field F] [NumberField F]

private theorem hat_sum {ι : Type} (s : Finset ι) (f : ι → S4 F) (x : V4 F) :
    hat (∑ i ∈ s, f i).1 x = ∑ i ∈ s, hat (f i).1 x := by
  induction s using Finset.induction_on with
  | empty =>
    have : ((0 : S4 F)).1 = (0 : ℂ) • (0 : V4 F → ℂ) := by simp
    simp only [Finset.sum_empty]
    rw [this, G.hat_smul, zero_mul]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact G.hat_add (f i) (∑ i ∈ s, f i) x

private theorem wt_mono {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [ite_eq_left hv, ite_eq_left (h hv)]
  · rw [ite_eq_right hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem wt_nonneg (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

end UpperTheory.ConvolutionTheory.R2.Ff.HM

end

open UpperTheory.ConvolutionTheory.R2.Ff.HM

theorem UpperTheory.ConvolutionTheory.R2.Ff.hatMaj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), HatMaj W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ y hy
  have hS := hatSt F E D W
  obtain ⟨n, e, he⟩ := omFin F E D W φ hφ
  have hb : ∀ i, ∃ K, IsCompact K ∧ ∀ N, ∃ B : ℝ, ∀ v,
      ‖hat (W.L (infGL E 2 y) (e i)).1 v‖ ≤ B * wt K N v := fun i => by
    obtain ⟨_, K, hK, h⟩ := wtBound F ⟨_, hS.mem (W.L (infGL E 2 y) (e i))⟩
    exact ⟨K, hK, fun N => by
      obtain ⟨B, hB⟩ := h N
      exact ⟨B, fun v => hB () trivial v⟩⟩
  choose K hK hB using hb
  refine ⟨⋃ i, K i, isCompact_iUnion hK, fun N => ?_⟩
  choose B hB' using fun i => hB i N
  refine ⟨∑ i, |B i|, fun b a k hk x u t => ?_⟩
  obtain ⟨c, hc, hk'⟩ := he k hk
  have hcomm : W.Om k (W.L (infGL E 2 y) φ) = W.L (infGL E 2 y) (W.Om k φ) := by
    have h := W.comm (infGL E 2 y) k
    rw [show nu F (infGL E 2 y) = 1 from hy, cD_one_left] at h
    exact (LinearMap.congr_fun h φ).symm
  have hΨ : W.Om k (W.L (infGL E 2 y) φ) = ∑ i, c i • W.L (infGL E 2 y) (e i) := by

    rw [hcomm, hk', map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hsplit : W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ) =
      W.Om (nU b) (W.Om (mD a) (∑ i, c i • W.L (infGL E 2 y) (e i))) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hΨ]
  have hv : Function.update ![(0 : A F), x, u, t] 1 (![(0 : A F), x, u, t] 1 + b * ![(0 : A F), x, u, t] 0) = ![0, x, u, t] := by
    funext i
    fin_cases i <;> simp
  have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
    have h0 := W.η_sq a
    have h : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
      first
        | (rw [← Units.val_pow_eq_pow_val, h0]; rfl)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, h, norm_one])
  set v' : V4 F := ![0, ((a⁻¹ : (A F)ˣ) : A F) * x, a * u, a * t] with hv'
  have hm : hat (W.Om (mD a) (∑ i, c i • W.L (infGL E 2 y) (e i))).1 ![0, x, u, t] =
      ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) * hat (∑ i, c i • W.L (infGL E 2 y) (e i)).1 v' := by
    rw [hS.m]
    simp [hv']
  have hsum : ‖hat (∑ i, c i • W.L (infGL E 2 y) (e i)).1 v'‖ ≤ (∑ i, |B i|) * wt (⋃ i, K i) N v' := by
    rw [hat_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h1 : hat (c i • W.L (infGL E 2 y) (e i)).1 v' = c i * hat (W.L (infGL E 2 y) (e i)).1 v' :=
      G.hat_smul _ _ _
    rw [h1, norm_mul]
    calc ‖c i‖ * ‖hat (W.L (infGL E 2 y) (e i)).1 v'‖
        ≤ 1 * (B i * wt (K i) N v') := mul_le_mul (hc i) (hB' i v') (norm_nonneg _) zero_le_one
      _ ≤ |B i| * wt (⋃ i, K i) N v' := by
        rw [one_mul]
        exact (mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg _ _ _)).trans
          (mul_le_mul_of_nonneg_left (wt_mono (Set.subset_iUnion K i) N v') (abs_nonneg _))
  rw [hsplit, hS.n, hv, norm_mul, norm_ψ, one_mul, hm, norm_mul, norm_mul, hη, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (ab_pos a).le]
  calc ab a * ‖hat (∑ i, c i • W.L (infGL E 2 y) (e i)).1 v'‖
      ≤ ab a * ((∑ i, |B i|) * wt (⋃ i, K i) N v') := mul_le_mul_of_nonneg_left hsum (ab_pos a).le
    _ = (∑ i, |B i|) * ab a * wt (⋃ i, K i) N v' := by ring
