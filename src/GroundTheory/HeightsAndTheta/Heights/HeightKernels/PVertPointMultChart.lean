module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointNagata
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointResidue
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointMultChart
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def mvPolyUnitEquiv (R : Type*) [CommRing R] : MvPolynomial Unit R ≃+* Polynomial R :=
  let f : MvPolynomial Unit R →+* Polynomial R :=
    MvPolynomial.eval₂Hom Polynomial.C (fun _ : Unit => Polynomial.X)
  let g : Polynomial R →+* MvPolynomial Unit R :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X ())
  { toFun := f
    invFun := g
    left_inv := fun p => by
      have h : g.comp f = RingHom.id _ := by
        apply MvPolynomial.ringHom_ext
        · intro r; simp [f, g]
        · rintro ⟨⟩; simp [f, g]
      exact RingHom.congr_fun h p
    right_inv := fun q => by
      have h : f.comp g = RingHom.id _ := by
        apply Polynomial.ringHom_ext
        · intro r; simp [f, g]
        · simp [f, g]
      exact RingHom.congr_fun h q
    map_mul' := f.map_mul
    map_add' := f.map_add }

def mNagataUnitEquiv (R : Type*) [CommRing R] [IsLocalRing R] :
    Targets.mNagataRing Unit R ≃+* nagataRing R := by
  let e : MvPolynomial Unit R ≃+* Polynomial R := mvPolyUnitEquiv R
  have hM : Ideal.map e.toRingHom
      ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial Unit R)) =
      (IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R) := by
    rw [Ideal.map_map]
    congr 1
    ext r
    simp [e, mvPolyUnitEquiv]
  have hS : Submonoid.map e.toMonoidHom
      ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial Unit R)).primeCompl =
      ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R)).primeCompl := by
    ext q
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨p, hp, rfl⟩ h
      rw [← hM] at h
      obtain ⟨p', hp', he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp h
      exact hp (e.injective he ▸ hp')
    · intro hq
      refine ⟨e.symm q, fun h => hq ?_, e.apply_symm_apply q⟩
      rw [← hM]
      have h' := Ideal.mem_map_of_mem e.toRingHom h
      simpa using h'
  exact IsLocalization.ringEquivOfRingEquiv (Targets.mNagataRing Unit R) (nagataRing R) e hS

theorem mNagataUnitEquiv_algebraMap {R : Type*} [CommRing R] [IsLocalRing R] (p : MvPolynomial Unit R) :
    mNagataUnitEquiv R (algebraMap (MvPolynomial Unit R) (Targets.mNagataRing Unit R) p) =
      algebraMap (Polynomial R) (nagataRing R) (mvPolyUnitEquiv R p) := by
  unfold mNagataUnitEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

theorem VertPointMultChart.proof (hCh : VertPointChart.Statement) (hN : VertPointNagata.Statement) :
    VertPointMultChart.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW t ht a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh T K' y s hP hs hsP W hW t ht
  exact Targets.CurveVertPointMultChart.of_single hs hW (fun _ => t) (fun _ => ht) a b hb
    (by simpa using hab) hmax (fun p => hrat p.2) fun a' b' hb' hab' => by
      obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN T K' y s hP hs hsP W hW t ht
        (fun u => a' ⟨(), u⟩) (fun u => b' ⟨(), u⟩) (fun u => hb' ⟨(), u⟩) (fun u => hab' ⟨(), u⟩)
      let η := mNagataUnitEquiv (Localization.AtPrime (curvePtIdeal y W))
      refine ⟨η.symm.toRingHom.comp Φ, η.symm.surjective.comp hsurj, ?_, fun f => ?_⟩
      · ext x
        rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff η.symm.toRingHom η.symm.injective,
          ← RingHom.mem_ker, hker]
      · rw [RingHom.comp_apply, hΦ f]
        apply η.injective
        change η (η.symm _) = mNagataUnitEquiv _ (algebraMap _ _ _)
        rw [η.apply_symm_apply, mNagataUnitEquiv_algebraMap]
        congr 1
        symm
        have hm : ∀ q, mvPolyUnitEquiv (Localization.AtPrime (curvePtIdeal y W)) q =
            MvPolynomial.eval₂Hom Polynomial.C (fun _ : Unit => Polynomial.X) q := fun _ => rfl
        induction f using MvPolynomial.induction_on with
        | C n =>
          rw [aeval_C, aeval_C]
          exact RingHom.congr_fun (RingHom.ext_int
            ((mvPolyUnitEquiv _).toRingHom.comp (algebraMap ℤ _)) (algebraMap ℤ _)) n
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p i hp =>
          rcases i with ⟨⟨⟩, u⟩
          rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, hm, map_mul, eval₂Hom_C, eval₂Hom_X']

end

end GroundTheory.Heights₂.Heights
