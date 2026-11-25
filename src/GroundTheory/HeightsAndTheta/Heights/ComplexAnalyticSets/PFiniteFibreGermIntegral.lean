module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassFiniteness
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRueckertNullstellensatz
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter

theorem FiniteFibreGermIntegral.proof (hWF : WeierstrassFiniteness.Statement)
    (hR : RueckertNullstellensatz.Statement) : FiniteFibreGermIntegral.Statement := by
  intro σ _ X x d A hX hiso g hg
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  let F : Fin (k + d) → (σ → ℂ) → ℂ := Fin.append f (fun j z => A z j - A x j)
  obtain ⟨n, a, h, ha, -, hrel⟩ := hWF σ x k f d A (fun i => hf i x hxN) (by
    intro l
    obtain ⟨m, c, -, hc, hsum⟩ := hR σ x (k + d) F (fun z => z l - x l) (by
      intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa only [F, Fin.append_left] using hf i x hxN
      · simp only [F, Fin.append_right]
        exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt x).sub analyticAt_const)
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) l).analyticAt x).sub analyticAt_const) (by
        filter_upwards [hNo.mem_nhds hxN, hW] with z hzN hzW h0
        suffices hz : z = x by simp [hz]
        refine hWiso z ⟨?_, hzW⟩ ?_
        · exact ((Set.ext_iff.mp hXN z).2 ⟨hzN, fun i => by
            simpa only [F, Fin.append_left] using h0 (Fin.castAdd d i)⟩).1
        · exact funext fun j => by
            simpa only [F, Fin.append_right, sub_eq_zero] using h0 (Fin.natAdd k j))
    refine ⟨m, fun i => c (Fin.castAdd d i), fun j => c (Fin.natAdd k j), fun i => hc _, fun j => hc _, ?_⟩
    simpa only [Fin.sum_univ_add, F, Fin.append_left, Fin.append_right] using hsum) g hg
  refine ⟨n, a, ha, ?_⟩
  filter_upwards [hrel, hNo.mem_nhds hxN] with z hz hzN hzX
  rw [hz]
  simp [((Set.ext_iff.mp hXN z).1 ⟨hzX, hzN⟩).2]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
