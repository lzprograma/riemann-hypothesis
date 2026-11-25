module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopNorm
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.SelfDual

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

namespace SD

theorem mm_unimod (x : D.host.E) :
    x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ↔
      ∀ y ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
        Algebra.trace D.host.K D.host.E (x * D.host.conj y) ∈
          (algebraMap (𝓞 D.host.K) D.host.K).range :=
  D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 x

variable {D}

theorem stdH_eq {N : ℕ} (x y : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N x y) = ∑ i, D.host.conj (x i) * y i :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.SD.stdH_eq (D := Formalism.L2.Ker.Car.ofRec D) x y

end SD

namespace CS

theorem s_sq : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem K_repr (x : D.host.E) (hx : x ∈ D.host.K) :
    ∃ p q : ℚ, x = (p : D.host.E) + (q : D.host.E) * D.host.sqd :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.CS.K_repr (Formalism.L2.Ker.Car.ofRec D) x hx

theorem embedding_sqrt_neg_d : D.host.φ₀ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  D.host.φ₀_mem

end CS

theorem self_dual_lattice : SelfDualRec :=
  fun D => Formalism.L2.Ker.Cd.IntegralLatticeDensity.self_dual_lattice (Formalism.L2.Ker.Car.ofRec D)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
