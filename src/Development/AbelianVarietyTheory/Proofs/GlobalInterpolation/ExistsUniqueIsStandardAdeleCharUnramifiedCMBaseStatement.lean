module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBase

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ := by
  first | exact @GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm
