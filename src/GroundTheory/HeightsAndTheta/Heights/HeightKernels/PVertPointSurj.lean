module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointSurj
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem VertPointSurj.proof (hC : CurveCharts.Statement) (hSQ : SectionQuotLocal.Statement) :
    VertPointSurj.Statement := by
  intro T _ K' _ _ y s hP hs hsP m hm hlen
  obtain ⟨hfin, -, hch⟩ := hC T K' y hP
  obtain ⟨t, hyt, hrat⟩ := hch m hm
  exact Targets.CurveVertPointSurj.of_single (K := Unit) (ι := fun _ => T) y s (fun _ => 1)
    hs hsP m hm hfin (fun _ => t) (fun _ => hyt) (fun p => hrat p.2) fun a b hbx => by
    simp only [Fintype.prod_unique, pow_one] at hbx
    rwa [← hSQ T K' y s hP hs hsP m t hm.isPrime hrat a b b.2 hbx]

end

end GroundTheory.Heights₂.Heights
