module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChart
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatChartP

open GlobalTheory.CompanionTheory.ChartAlg

theorem exists_flat_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  apply GlobalTheory.CompanionTheory.ChartP.exists_chart

end GlobalTheory.CompanionTheory.FlatChartP
