module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

noncomputable section

namespace GlobalTheory.SWC

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

def hermCoord {n : ℕ} (S : HermR R σ n) : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
  (fun a => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 a a), fun p => S.1 p.1.1 p.1.2)

variable [TopologicalSpace R] {M n : ℕ}

end Local

end GlobalTheory.SWC

end
