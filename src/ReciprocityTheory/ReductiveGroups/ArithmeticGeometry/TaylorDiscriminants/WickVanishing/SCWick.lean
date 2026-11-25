module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LiftXHasSubst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.WickFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondOrderIterateEqZero

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem betaH_zero_zero (φ φ' : Fin d → k) : betaH k (0, φ) (0, φ') = 0 := by
  simp [betaH]

theorem betaH_antisymm (ξ η : (Fin d → k) × (Fin d → k)) : betaH k ξ η = -betaH k η ξ := by
  unfold betaH
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

def kapW (m : ℕ) {ι : Type} (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (l l' : ι) : k :=
  if s l = true ∧ s l' = false then (m : k) * betaH k (ξb l) (ξa l') else 0

theorem kapW_supp (m : ℕ) {ι : Type} (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (l l' : ι)
    (h : kapW m s ξa ξb l l' ≠ 0) : s l = true ∧ s l' = false := by
  unfold kapW at h
  by_contra hc
  exact h (ite_eq_right hc)

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
