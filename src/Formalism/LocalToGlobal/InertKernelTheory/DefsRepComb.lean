module

public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.RepComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

abbrev hK (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a b : ℕ) : Sesq (TaylorLogMetric.VC D a b) :=
  HV (ι := D.what₂.Tau) (a := a) (b := b) (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹

abbrev alK (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a b : ℕ) : TaylorLogMetric.VC D a b → ℂ :=
  alV (ι := D.what₂.Tau) (a := a) (b := b) D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹


variable (cc δ) in
abbrev lamK {a b : ℕ} (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  LamC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N'


variable (cc δ) in
abbrev halfA {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  AC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl


variable (cc δ) in
abbrev halfB {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  BC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl


variable (cc δ) in
def FinIdx {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Prop :=
  relIdx (lamK cc δ N N') (halfA cc δ SS cl N N') ≠ 0 ∧
    relIdx (halfB cc δ SS cl N N') (lamK cc δ N N' ⊓ halfA cc δ SS cl N N') ≠ 0 ∧
    relIdx (lamK cc δ N N') (halfB cc δ SS cl N N') ≠ 0


variable (cc δ) in
def LamIn {a b : ℕ} (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Prop :=
  lamK cc δ N N' ≤ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N'

def CombKerT : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]),
    TaylorLogMetric.admitted D a b N N' → N'.FG → Submodule.span D.host.E (N : Set (Formalism.L2.Col.Sp D.host.E a)) = ⊤ →
    (Formalism.L2.PairingIndexBounds.F.aaOf D cc).FG →
    LaFacts (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' →
    0 < cl → SNum S cl → (∀ x, IntOff S (Ξ x)) → p ∉ S → LamIn cc δ N N' → TransAlg D B.tor (B.eNat χ) →
      TaylorLogMetric.IsComb D B.tor (B.eNat χ) lam N N' (Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ))

end Formalism.L2.KerInert.RepComb
