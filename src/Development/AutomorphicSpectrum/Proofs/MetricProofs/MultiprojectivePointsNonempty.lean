module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsIntDim
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphFibreRatio

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem exists_ratAlgHom_complex (A : Type) [CommRing A] [Nontrivial A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    Nonempty (A →ₐ[ℚ] ℂ) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
  let κ : (A ⧸ M) →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨κ.comp (Ideal.Quotient.mkₐ ℚ M)⟩

theorem aeval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {x : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal x) : aeval x f = 0 := by
  apply _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphFibreRatio.aeval_eq_zero_of_mem <;> assumption

theorem mcPts_mCoordIdeal_nonempty (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (x : (Σ k, ι k) → Ω) (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) : (mcPts (mCoordIdeal x)).Nonempty := by
  choose c hc using hx
  set u : Ω := ∏ k, x ⟨k, c k⟩ with hu
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  let S : Set Ω := Set.range x ∪ {u⁻¹}
  have hS : S.Finite := (Set.finite_range x).union (Set.finite_singleton _)
  let A : Subalgebra ℚ Ω := Algebra.adjoin ℚ S
  have : Algebra.FiniteType ℚ A := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨ρ⟩ := exists_ratAlgHom_complex A
  let xA : (Σ k, ι k) → A := fun p => ⟨x p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩
  let v : A := ⟨u⁻¹, Algebra.subset_adjoin (Or.inr rfl)⟩
  have huv : (∏ k, xA ⟨k, c k⟩) * v = 1 := by
    apply Subtype.ext
    have : ((∏ k, xA ⟨k, c k⟩ : A) : Ω) = u := by
      rw [hu]
      exact map_prod A.val _ _
    show ((∏ k, xA ⟨k, c k⟩ : A) : Ω) * u⁻¹ = 1
    rw [this, mul_inv_cancel₀ hu0]
  have hz : (∏ k, ρ (xA ⟨k, c k⟩)) * ρ v = 1 := by
    rw [← map_prod, ← map_mul, huv, map_one]
  refine ⟨fun p => ρ (xA p), fun k => ⟨c k, fun h0 => ?_⟩, fun f hf => ?_⟩
  · have : ∏ k, ρ (xA ⟨k, c k⟩) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [this, zero_mul] at hz
    exact zero_ne_one hz
  · have h1 : aeval xA f = 0 := Subtype.ext <| by
      change (A.val.restrictScalars ℤ) (aeval xA f) = 0
      rw [MvPolynomial.comp_aeval_apply]
      exact aeval_eq_zero_of_mem_mCoordIdeal hf
    have h2 := MvPolynomial.map_aeval_eq_aeval_map (Int.castRingHom ℂ)
      ρ.toRingHom (RingHom.ext_int _ _) f xA
    rw [h1, map_zero] at h2
    exact h2.symm

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
