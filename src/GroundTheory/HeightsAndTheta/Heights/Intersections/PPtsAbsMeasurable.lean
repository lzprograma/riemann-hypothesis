module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsMeasurable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeD
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Set Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace PointsAbsMeasurable

section PushForward

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem integrable_absPushSum [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, |g x * pushDens A Φ q x|) :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.pushForward_integrable_comp A Φ hΦ q S hS hq hfin g hg abs
    (fun a b hb => by rw [abs_div, abs_of_nonneg hb])
    (fun c r hc => by rw [abs_mul, abs_of_nonneg hc])
    (fun hf => hf.abs)

end PushForward

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem absFibreSum_ae (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        |logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x| := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    measure_eq_zero_iff_ae_notMem.mp hN
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono (by exact fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩))]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dite_eq_left ⟨γ, hγ⟩]
  exact congrArg abs
    ((hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval)

end Res

end PointsAbsMeasurable


open PointsAbsMeasurable in
theorem PtsAbsMeasurable.proof (hE : ResExistsStatement) : PtsAbsMeasurable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  have hI := integrable_absPushSum R.A (fun j => potOf R (L j))
    (fun j => potOf_isPotential R (L j) (hL j)) (brQ R Ψ) (brBad R Ψ) (brBad_null R Ψ hP hΨ)
    (brGood R Ψ) (brFib_finite R Ψ hP hΨ) _ (brIntegrable R L A s hP hL hA hs)
  exact hI.aestronglyMeasurable.congr
    ((absFibreSum_ae R Ψ L A s hP hΨ hL hA hs).mono fun y hy => hy.symm)

end GroundTheory.Heights₂.Heights.Inter
