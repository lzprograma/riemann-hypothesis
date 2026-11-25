module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFSMass
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionPotentials
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegreeIntegral
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

namespace ResolutionDegree

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem mass_pullFS (hPM : ProjFSMass.Statement) (d : HSMDatum D Ω κ) {e : Fin (D + 1) → Ix κ}
    {m₀ : ConeMetric ℂ (Ix κ)} (hfr : IsProjFrame d.x e) (h₀ : IsSmoothMetric m₀) (hFS : IsPullFS d.x e m₀) :
    mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) = (projDeg d.x e : ℝ) := by
  obtain ⟨Ψ, hΨ, hmass⟩ := hPM D Ω κ d.x e m₀ hfr hFS
  let A : HermLine (GlobalTheory κ) := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  have hA : IsSmoothHerm A := contDiffOn_const
  have hlog : logNorm A 1 = fun _ => (1 : ℝ) := by
    funext z
    simp [A, logNorm, HermLine.ofWeight]
  have hsec : IsSectionOn (coordIdeal ℤ d.x) A 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro a ha k
      rw [support_one] at ha
      simp only [Finset.mem_singleton] at ha
      simp [ha]
    · exact (Ideal.ne_top_iff_one _).1 d.arith.2.1.1.ne_top
  have key := AnResBridge.bridge d.R Ψ (fun _ => HermLine.ofCone m₀) A 1 d.arith hΨ
    (fun _ => gbamix_smoothHerm_ofCone h₀) hA hsec
  rw [hlog] at key
  rw [← hmass]
  exact key.symm

end ResolutionDegree

theorem ResolutionDegree.proof (hPF : PullFSExtension.Statement) (hPM : ProjFSMass.Statement) :
    ResolutionDegree.Statement := by
  intro D Ω _ _ κ _ d e m hfr hm
  obtain ⟨m₀, h₀, -, -, hFS⟩ := hPF D Ω κ d.x e hfr
  rw [BlockResolutionDegreeIntegral.mass_eq d.R (A₀ := HermLine.ofCone m₀) (A₁ := HermLine.ofCone m)
    rfl (gbamix_smoothHerm_ofCone h₀) (gbamix_smoothHerm_ofCone hm) 1
    (fun _ _ _ => by show Real.log (m.ρ _) = (1 - 1) * Real.log (m₀.ρ _) + 1 * Real.log (m.ρ _); ring)]
  exact ResolutionDegree.mass_pullFS hPM d hfr h₀ hFS

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
