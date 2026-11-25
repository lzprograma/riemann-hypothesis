module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
public import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

@[expose] public section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.L1

private theorem centComm_field {k : Type} [Field k] {n : ℕ} (γ a b : GL (Fin n) k)
    (hs : (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (ha : a ∈ Subgroup.centralizer {γ}) (hb : b ∈ Subgroup.centralizer {γ}) : a * b = b * a := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hA : Commute (a : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val ha
  have hB : Commute (b : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val hb
  exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm k n _ _ _ hs hA hB)

private theorem regOk_field (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    (n : ℕ) : RegOk k n := by
  intro γ hs
  refine ⟨?_, fun a ha b hb => centComm_field γ a b hs ha hb⟩
  have e : {y : GL (Fin n) k | ∃ x : GL (Fin n) k, y = x⁻¹ * γ * x} =
      ⋂ i : ℕ, {y : GL (Fin n) k | (y : Matrix (Fin n) (Fin n) k).charpoly.coeff i =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨x, rfl⟩ i
      have h := Matrix.charpoly_units_conj x⁻¹ (γ : Matrix (Fin n) (Fin n) k)
      rw [← Matrix.coe_units_inv, inv_inv] at h
      rw [Units.val_mul, Units.val_mul]
      exact congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) h
    · intro h
      exact GlobalTheory.BCT.ClsFin.conj_of_charpoly γ y hs (Polynomial.ext h).symm
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq
    ((GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff i).comp Units.continuous_val)
    continuous_const

section Pi

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] {n : ℕ}

private abbrev ev (i : I) : GL (Fin n) (∀ i, k i) →* GL (Fin n) (k i) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom k i)

private def piGL : GL (Fin n) (∀ i, k i) ≃* ∀ i, GL (Fin n) (k i) :=
  (Units.mapEquiv Matrix.piRingEquiv.toMulEquiv).trans MulEquiv.piUnits

end Pi

private theorem regOk_pi (I : Type) (k : I → Type) [∀ i, Field (k i)] [∀ i, TopologicalSpace (k i)]
    [∀ i, IsTopologicalRing (k i)] [∀ i, T2Space (k i)] (n : ℕ) : RegOk (∀ i, k i) n := by
  intro γ hs
  have hsi : ∀ i, ((ev i γ : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)).charpoly.Separable := fun i => by
    change ((γ : Matrix (Fin n) (Fin n) (∀ i, k i)).map (Pi.evalRingHom k i)).charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hs.map
  have hc : ∀ i, Continuous (ev (n := n) (k := k) i) := fun i =>
    (continuous_apply i : Continuous (Pi.evalRingHom k i)).generalLinearGroup_map
  refine ⟨?_, fun a ha b hb => (piGL (k := k)).injective (funext fun i => ?_)⟩
  · have e : {y : GL (Fin n) (∀ i, k i) | ∃ x : GL (Fin n) (∀ i, k i), y = x⁻¹ * γ * x} =
        ⋂ i, (ev i) ⁻¹' {y : GL (Fin n) (k i) | ∃ x : GL (Fin n) (k i), y = x⁻¹ * ev i γ * x} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      constructor
      · rintro ⟨x, rfl⟩ i
        exact ⟨ev i x, by simp only [map_mul, map_inv]⟩
      · intro h
        choose x hx using h
        refine ⟨piGL.symm x, (piGL (k := k)).injective (funext fun i => ?_)⟩
        simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, MulEquiv.apply_symm_apply]
        exact hx i
    rw [e]
    exact isClosed_iInter fun i => ((regOk_field (k i) n (ev i γ) (hsi i)).1).preimage (hc i)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    have hA : Commute (ev i a) (ev i γ) := by
      change (ev i a) * (ev i γ) = (ev i γ) * (ev i a)
      simpa only [map_mul] using congrArg (ev i) ha
    have hB : Commute (ev i b) (ev i γ) := by
      change (ev i b) * (ev i γ) = (ev i γ) * (ev i b)
      simpa only [map_mul] using congrArg (ev i) hb
    have ha' : ev i a ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hA
    have hb' : ev i b ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hB
    have hab : ev i a * ev i b = ev i b * ev i a :=
      centComm_field (ev i γ) (ev i a) (ev i b) (hsi i) ha' hb'
    rw [map_mul, map_mul]
    exact hab

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.regOkPi :
    UpperTheory.ConvolutionTheory.L1.RegOkPi :=
  ⟨fun k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_field k n, fun I k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi I k n,
    fun F _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi (NumberField.InfinitePlace F) (fun v => v.Completion) n⟩
