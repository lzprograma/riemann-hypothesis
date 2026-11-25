module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact", "h": "module\n\npublic import Formalism.SatakeDualWeyl.Statement\npublic import Formalism.FormalDegreeBessel.StatementG\npublic import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.DefiniteFrame

theorem exists_frame {n p q : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature J p q) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det ∧
      J = Bᴴ * (Formalism.UG.Jpq p q).submatrix e e * B := by
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e J) * P.val = Formalism.UG.Jpq p q := hP
  refine ⟨e, (P⁻¹).val.submatrix e e, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  · have h1 := Units.mul_inv P
    have h2 : (P⁻¹).valᴴ * P.valᴴ = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, ← hP']
    have h3 : (P⁻¹).valᴴ *
        (P.valᴴ * (reindex e e J) * P.val) *
        (P⁻¹).val = reindex e e J := by
      calc _ = ((P⁻¹).valᴴ * P.valᴴ) * (reindex e e J) *
          (P.val * (P⁻¹).val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [h3]
    ext i j
    simp

theorem isCompact_UH_gram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    IsCompact (Formalism.QuantumDeterminants.UH (Bᴴ * B)) := by
  have hc : Continuous fun u : Matrix (Fin n) (Fin n) ℂ => B⁻¹ * u * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  have h1' : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  have h2 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2' : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1', conjTranspose_one]
  convert (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).image hc using 1
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe,
    Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  constructor
  · intro hg
    refine ⟨B * g * B⁻¹, ?_, ?_⟩
    · calc (B * g * B⁻¹)ᴴ * (B * g * B⁻¹) = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * B) * g) * B⁻¹ := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) := by rw [hg]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, h2, Matrix.one_mul]
    · calc B⁻¹ * (B * g * B⁻¹) * B = (B⁻¹ * B) * g * (B⁻¹ * B) := by
            simp only [Matrix.mul_assoc]
        _ = g := by rw [h1', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨u, hu, rfl⟩
    calc (B⁻¹ * u * B)ᴴ * (Bᴴ * B) * (B⁻¹ * u * B)
        = Bᴴ * (uᴴ * ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) * u) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hu, Matrix.mul_one]

theorem UH_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp [Formalism.QuantumDeterminants.UH]

theorem definite_frame (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.UG.HasSignature J p q) (hpq : p = 0 ∨ q = 0) :
    (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧
      IsCompact (Formalism.QuantumDeterminants.UH J) := by
  obtain ⟨e, B, hB, hJ⟩ := exists_frame h
  rcases hpq with rfl | rfl
  · have h1 : Formalism.UG.Jpq 0 q = -1 := by
      ext i j
      rcases i with i | i
      · exact i.elim0
      rcases j with j | j
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = -(Bᴴ * B) := by
      rw [hJ, h1, submatrix_neg]
      simp
    refine ⟨⟨B, hB, Or.inr h2⟩, ?_⟩
    rw [h2, UH_neg]
    exact isCompact_UH_gram B hB
  · have h1 : Formalism.UG.Jpq p 0 = 1 := by
      ext i j
      rcases i with i | i
      swap
      · exact i.elim0
      rcases j with j | j
      swap
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = Bᴴ * B := by
      rw [hJ, h1]
      simp
    refine ⟨⟨B, hB, Or.inl h2⟩, ?_⟩
    rw [h2]
    exact isCompact_UH_gram B hB

end GlobalTheory.DefiniteFrame
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Calculus.ContDiff.Defs\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_prod_ofFn_coord {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {ι : Type}
    (R : ι → ℝ → A) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (k : ℕ) (I : Fin k → ι) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun a => R (I a) (t a)).prod := by
  induction k with
  | zero => simpa using contDiff_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    refine ContDiff.mul ((hR (I 0)).comp (contDiff_apply ℝ (fun _ => ℝ) 0)) ?_
    have h : ContDiff ℝ ∞ fun (t : Fin (k + 1) → ℝ) (a : Fin k) => t a.succ :=
      contDiff_pi.2 fun a => contDiff_apply ℝ (fun _ => ℝ) a.succ
    exact (ih fun a => I a.succ).comp h

theorem smooth_of_finiteDimensional_translation_stable :
    ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  intro G _ M _ ι c hc hM hcont
  let V := Fin (Module.finrank ℂ M) → ℂ
  let Φ : M ≃L[ℂ] V := (Module.finBasis ℂ M).equivFun.toContinuousLinearEquiv
  let ρ : ι → ℝ → (M →ₗ[ℂ] M) := fun i t =>
    { toFun := fun f => ⟨fun g => f.1 (g * c i t), hM i t f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let R : ι → ℝ → (V →L[ℂ] V) := fun i t =>
    LinearMap.toContinuousLinearMap (Φ.toLinearEquiv.toLinearMap ∘ₗ ρ i t ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hRapp : ∀ i t v, R i t v = Φ (ρ i t (Φ.symm v)) := fun _ _ _ => rfl
  let ev : G → (V →L[ℂ] ℂ) := fun g =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj g : (G → ℂ) →ₗ[ℂ] ℂ) ∘ₗ M.subtype ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hev : ∀ g v, ev g v = (Φ.symm v).1 g := fun _ _ => rfl
  have hkey : ∀ g i t v, ev g (R i t v) = ev (g * c i t) v := by
    intro g i t v
    rw [hev, hRapp, Φ.symm_apply_apply]
    rfl
  have hsep : ∀ v w : V, (∀ g, ev g v = ev g w) → v = w := by
    intro v w h
    apply Φ.symm.injective
    exact Subtype.ext (funext h)
  have hc0 : ∀ i, c i 0 = 1 := by
    intro i
    have := hc i 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hR : ∀ i, ContDiff ℝ ∞ (R i) := by
    intro i
    refine _root_.GlobalTheory.contDiff_of_continuous_oneParameter _ (R i) ?_ ?_ ?_
    · refine continuous_clm_apply.2 fun v => ?_
      simp only [hRapp]
      refine Φ.continuous.comp ?_
      exact Continuous.subtype_mk (continuous_pi fun g => hcont i _ (Φ.symm v).2 g) _
    · refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [hkey, hc0, mul_one]; rfl
    · intro s t
      refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [ContinuousLinearMap.mul_apply, hkey, hkey, hkey, hc, mul_assoc]
  have hf : ∀ f (hf : f ∈ M) g, f g = ev g (Φ ⟨f, hf⟩) := by
    intro f hf g
    rw [hev, Φ.symm_apply_apply]
  refine ⟨fun i f hfM => ?_, fun k I f hfM g => ?_⟩
  · have hd : HasDerivAt (R i) (deriv (R i) 0) 0 :=
      ((hR i).differentiable (by simp) 0).hasDerivAt
    have : (fun g => deriv (fun t : ℝ => f (g * c i t)) 0)
        = (Φ.symm (deriv (R i) 0 (Φ ⟨f, hfM⟩))).1 := by
      funext g
      rw [← hev]
      have h1 : (fun t : ℝ => f (g * c i t)) = fun t => ev g (R i t (Φ ⟨f, hfM⟩)) := by
        funext t
        rw [hkey, ← hf]
      rw [h1]
      let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
      exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv
    rw [this]
    exact Subtype.property _
  · have hprod : ∀ (k : ℕ) (I : Fin k → ι) (t : Fin k → ℝ) (g : G) (v : V),
        ev g ((List.ofFn fun a => R (I a) (t a)).prod v)
          = ev (g * (List.ofFn fun a => c (I a) (t a)).prod) v := by
      intro k
      induction k with
      | zero => intro I t g v; simp
      | succ k ih =>
        intro I t g v
        simp only [List.ofFn_succ, List.prod_cons]
        rw [ContinuousLinearMap.mul_apply, hkey, ih (fun a => I a.succ) (fun a => t a.succ),
          mul_assoc]
    have h1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod))
        = fun t => ev g ((List.ofFn fun a => R (I a) (t a)).prod (Φ ⟨f, hfM⟩)) := by
      funext t
      rw [hprod, ← hf]
    rw [h1]
    let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
    exact (L.restrictScalars ℝ).contDiff.comp (contDiff_prod_ofFn_coord R hR k I)

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple\npublic import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList\npublic import Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef\npublic import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau\npublic import Formalism.SatakeDualWeyl.Statement\npublic import Formalism.FormalDegreeBessel.StatementG\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Calculus.Deriv.Basic\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\npublic import Mathlib.LinearAlgebra.Eigenspace.Basic\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalEigenspaceSumSqInvariantFieldsA\npublic import Mathlib.Basic.Complex.Basic\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKerAevalOfEigenspaces\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntertwineAeval\npublic import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite\npublic import Mathlib.Analysis.Calculus.ContDiff.Defs\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable\npublic import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.DefiniteForms

open GlobalTheory.SmoothForms Filter Topology
open scoped ContDiff

section Abstract

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

theorem mul_anti_of_unitary {a : 𝔸} (h : σ a * a = 1) : a * σ a = 1 := by
  have : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
  exact mul_eq_one_comm.1 h

theorem unitary_anti (H : IsLieData σ j s) {a : 𝔸} (ha : σ a * a = 1) : σ (σ a) * σ a = 1 := by
  rw [H.invol, mul_anti_of_unitary ha]

theorem continuousOn_of_sm (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (g : G) :
    ContinuousOn (fun u => φ (g * s u)) {u | σ u * u = 1} := by
  obtain ⟨Λ, h1, h2, -⟩ := hl
  intro u₀ hu₀
  have hu₀' : σ u₀ * u₀ = 1 := hu₀
  have hm : Continuous fun u : 𝔸 => σ u₀ * u := continuous_const.mul continuous_id
  have ht : Tendsto (fun u => σ u₀ * u) (𝓝 u₀) (𝓝 1) := by
    have := hm.tendsto u₀
    rwa [hu₀'] at this
  have h4 : ContinuousAt (fun u => Λ (σ u₀ * u)) u₀ :=
    ContinuousAt.comp (g := Λ) (by rw [hu₀']; exact h1.continuousAt) hm.continuousAt
  have h5 : ContinuousAt (fun u => φ (g * s u₀ * expMap j s (Λ (σ u₀ * u)))) u₀ :=
    (hφ (g * s u₀)).continuous.continuousAt.comp h4
  have key : ∀ u, (σ (σ u₀ * u) * (σ u₀ * u) = 1 → NormedSpace.exp (j (Λ (σ u₀ * u))) = σ u₀ * u) → σ u * u = 1 →
      φ (g * s u) = φ (g * s u₀ * expMap j s (Λ (σ u₀ * u))) := fun u hp hu => by
    have hu' := _root_.GlobalTheory.SmoothForms.Bracket.unitary_mul H (unitary_anti H hu₀') hu
    rw [expMap, hp hu', mul_assoc, ← H.mul _ _ hu₀' hu', ← mul_assoc, mul_anti_of_unitary hu₀', one_mul]
  refine h5.continuousWithinAt.congr_of_eventuallyEq ?_ (key u₀ (ht.eventually h2).self_of_nhds hu₀')
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ht.eventually h2), self_mem_nhdsWithin] with u a b using key u a b

theorem expMap_add (H : IsLieData σ j s) (X : L) (a b : ℝ) :
    expMap j s ((a + b) • X) = expMap j s (a • X) * expMap j s (b • X) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold expMap
  rw [← H.mul _ _ (DerLinear.exp_unitary H _) (DerLinear.exp_unitary H _), ← NormedSpace.exp_add_of_commute, add_smul,
    map_add]
  rw [map_smul, map_smul]
  exact ((Commute.refl _).smul_left _).smul_right _

end Abstract

section Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Matrix
open scoped TensorProduct

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem frame_at (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    (∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B.det ∧ (gramAt D V τ = Bᴴ * B ∨ gramAt D V τ = -(Bᴴ * B))) ∧
      IsCompact (Formalism.QuantumDeterminants.UH (gramAt D V τ)) :=
  _root_.GlobalTheory.DefiniteFrame.definite_frame _ _ _ _ (hs (tauE D τ)) (by rcases hd (tauE D τ) with h | h <;> simp [h])

theorem isCompact_unitary (R : RealPoints θ V) (hs : V.SigOK) (hd : V.IsDefinite) :
    IsCompact {u : AlgInf V | sigInf V u * u = 1} := by
  have h := isCompact_univ_pi fun τ => (frame_at hs hd τ).2
  have e : {u : AlgInf V | sigInf V u * u = 1} = Set.univ.pi fun τ => Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    Set.ext fun u => (unit_iff R u).trans ⟨fun h τ _ => h τ, fun h τ => h τ trivial⟩
  rw [e]
  exact h

theorem exists_secInf (hθ : IsInfFam θ) (R : RealPoints θ V) {g : GA D V} (hg : g ∈ GinfC V) :
    ∃ u : AlgInf V, sigInf V u * u = 1 ∧ secInf θ V u = g := by
  have hu := (unit_iff R fun τ => infMat D.sp.cm.sig V.gram (θ τ) g).2
    fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  exact ⟨_, hu, R.2.2.1 _ (secInf_spec R hu).1 _ hg (secInf_spec R hu).2⟩

theorem foldr_mem {α M : Type} {S : Set M} (T : α → M → M) (l : List α) (hl : ∀ a ∈ l, ∀ f ∈ S, T a f ∈ S) {f : M}
    (hf : f ∈ S) : l.foldr (fun a f => T a f) f ∈ S := by
  induction l with
  | nil => exact hf
  | cons a l ih => exact hl a (by simp) _ (ih fun b hb => hl b (by simp [hb]))

theorem sm_of_kfin (hθ : IsInfFam θ) (hs : V.SigOK) (hd : V.IsDefinite) {φ : GA D V → ℂ} (h : IsAutFunDef V φ) :
    IsAutFunSm θ V φ := by
  have R := RealPts.realPoints D |>.2 θ hθ V
  have hfd := h.kfin
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  set M := Submodule.span ℂ {ψ : GA D V → ℂ | ∃ k ∈ GinfC V, ψ = rTr V k φ} with hM
  have hφ : φ ∈ M := Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp [rTr]⟩
  have hcont : ∀ f ∈ M, Continuous f := fun f hf => by
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨k, -, rfl⟩ := hx; exact h.cont.comp (continuous_mul_const k)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.const_smul c
  have hst : ∀ k ∈ GinfC V, ∀ f ∈ M, (fun g => f (g * k)) ∈ M := fun k hk f hf => by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      exact Submodule.subset_span ⟨k * k', mul_mem hk hk', funext fun g => by simp [rTr, mul_assoc]⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact M.smul_mem c hx
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.smooth_of_finiteDimensional_translation_stable (GA D V) M (Σ τ, LieAt V τ) (fun i t => oneP θ V i.1 i.2.1 t)
    (fun i a b => by
      simp only [oneP_eq R]
      exact expMap_add (isLieData R) _ a b)
    (fun i t => hst _ (GlobalTheory.PointAtPlaceHom.atTau_mem V _ _))
    (fun i f hf g => by
      refine (hcont f hf).comp (continuous_const.mul ?_)
      refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V i.1).comp_continuous ?_
        fun t => GlobalTheory.SmoothAutCheck.exp_mem_UH (R.1 i.1).2 i.2.2 t
      have := (continuous_apply i.1).comp ((DerLinear.contDiff_exp (isLieData R)).continuous.comp
        (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • (atPlace V i.1 i.2 : LieN V)))
      refine this.congr fun t => ?_
      classical
      refine (exp_algInf V _ _).trans ?_
      congr 1
      change t • (atPlace V i.1 i.2 i.1).1 = _
      rw [atPlace, Pi.single_eq_same])
  have hR : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f ∈ M, Rder θ V τ X f ∈ M := fun τ X hX => h1 ⟨τ, X, hX⟩
  have hsm : ∀ f ∈ M, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf k τs Xs hX g =>
    h2 k (fun a => ⟨τs a, Xs a, hX a⟩) f hf g
  refine ⟨h.toIsAutFun, hsm φ hφ, ⟨M, hfd, hφ, fun τ k f hf => ?_⟩, 0, fun l hl x => ?_⟩
  · refine sum_mem fun idx _ => foldr_mem (S := (M : Set _)) (fun T : (GA D V → ℂ) → GA D V → ℂ => T) _
      (fun T hT f hf => ?_) hf
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hT
    obtain ⟨m1, m2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ (Matrix.single (idx a) (idx (a + 1)) 1)
    exact add_mem (hR τ _ m1 f hf) (M.smul_mem _ (hR τ _ m2 f hf))
  · have hf := foldr_mem (S := (M : Set _))
      (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l (fun p hp => hR p.1 p.2 (hl p hp)) hφ
    obtain ⟨C, hC⟩ := (isCompact_unitary R hs hd).exists_bound_of_continuousOn
      (continuousOn_of_sm (isLieData R) (hasLog R) ((smooth_iff R _).1 (hsm _ hf)) x)
    refine ⟨C, fun g hg => ?_⟩
    obtain ⟨u, hu, rfl⟩ := exists_secInf hθ R hg
    rw [pow_zero, mul_one]
    exact hC u hu

end Adelic

end GlobalTheory.DefiniteForms

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary =====
