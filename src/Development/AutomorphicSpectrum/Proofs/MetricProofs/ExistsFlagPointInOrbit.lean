module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem exists_flagPt_of_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) (BM.Rb.lift b b) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.flagPt M (BM.F l) (FC.bvec BM l b) h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb z hz hzb
  obtain ⟨hβmem, hβgood, hβc, hβorb⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  have h1 : SameOrbit (basePart M.blk z) (bvec BM l b) :=
    Cj.sameOrbit_trans hzb (Cj.sameOrbit_symm hβorb)
  obtain ⟨d, hd, hdz⟩ := id h1
  have hne : ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k
    rw [hdz]
    show d k * bvec BM l b ⟨k, (BM.F l).c k⟩ ≠ 0
    rw [hβc k, mul_one]
    exact hd k
  obtain ⟨z₁, hz₁z, hz₁c⟩ := GlobalTheory.CompanionTheory.Ar.PB.FibreCount.exists_normal_base M.blk (BM.F l).c z hne
  have hb1 : SameOrbit (basePart M.blk z₁) (bvec BM l b) :=
    Cj.sameOrbit_trans (GlobalTheory.CompanionTheory.Ar.PB.FibreCount.basePart_orbit M.blk hz₁z)
      h1
  have hbeq : basePart M.blk z₁ = bvec BM l b := by
    obtain ⟨e, he, hez⟩ := hb1
    have he1 : ∀ k, e k = 1 := by
      intro k
      have hk := congrFun hez ⟨k, (BM.F l).c k⟩
      have hk' : basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = e k * bvec BM l b ⟨k, (BM.F l).c k⟩ := hk
      rw [hz₁c k, hβc k, mul_one] at hk'
      exact hk'.symm
    rw [hez]
    funext p
    show e p.1 * bvec BM l b p = bvec BM l b p
    rw [he1, one_mul]
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := by
    obtain ⟨c, hc, hcz⟩ := id hz₁z
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := hz.1 k
      refine ⟨i, ?_⟩
      rw [hcz]
      exact mul_ne_zero (hc k) hi
    · intro f hf
      have hf' : f ∈ mCoordIdeal z₁ := by
        rw [GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit hz₁z]
        exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hz hf
      exact _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.eval_eq_zero_of_mem hf'
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hbeq]
    exact hβgood
  obtain ⟨h, hflag⟩ := GlobalTheory.CompanionTheory.Ar.PB.CPts.flag_fwd M (BM.isFrame l) hz₁ hgood hz₁c
  obtain ⟨_, hhb, hblocks⟩ := hflag
  refine ⟨h, hhb, ?_⟩
  have h2 : SameOrbit z₁ (flagPt M (BM.F l) (bvec BM l b) h) := by
    apply GlobalTheory.CompanionTheory.Ar.PB.FibreCount.sameOrbit_of_blocks M.blk
    · rw [basePart_flagPt, hbeq]
    · intro p k hpk
      obtain ⟨a, ha, hza⟩ := hblocks p k hpk
      refine ⟨a, ha, fun m => ?_⟩
      rw [hza m, flagPt_step M (BM.F l) (bvec BM l b) h hpk m, hbeq]
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm hz₁z) h2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
