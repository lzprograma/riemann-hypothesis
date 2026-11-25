module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorLevelMultiplicitySpaceMemGoodRows
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical

namespace GlobalTheory.Fam.PlaceSep

variable {D : D7}

theorem natCast_mem_of_under_eq {PP PP' : Pl D.host.E}
    (h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) {n : ℕ} (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  have h1 : ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  rw [h] at h1
  have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP'.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (u : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * ((q : ℕ) : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem twist_prime {gp : Fin 2 → ℕ} {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces gp Q) {PP : Pl D.host.E} (hP : PP ∈ Q) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ gp i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP hP
  refine ⟨q, hq, ?_, hne⟩
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, show Nat.card (𝓞 D.host.E ⧸ PP.asIdeal) = q from hc] at this

theorem g_mem_of_div (P : Formalism.L2.Host.PiBar D.host) {k : Fin 2} {w : Pl D.host.E} (hw : P.Div k w) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 := P.pb_over k
  rw [← hw] at h1
  have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at this

end GlobalTheory.Fam.PlaceSep
