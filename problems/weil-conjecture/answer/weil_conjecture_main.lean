import WeilPart45
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry

theorem weil_frob_eigenvalues_of_projective_alteration (F : Type u) [Finite F] [Field F]
    (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of F)))
    [AlgebraicGeometry.GeometricallyIrreducible X.hom]
    [AlgebraicGeometry.IsProper X.hom]
    (d : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension d X.hom]
    (hAlt : HasSmoothProjectiveAlteration F d X) :
    ∃ A : ℕ → Multiset ℂ, A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map (Nat.card F ^ d / · : ℂ → ℂ)) ∧
      (∀ n : ℕ, 1 ≤ n →
        (weilPointCount F X n : ℂ) =
          ∑ i ∈ Finset.Iic (2 * d), (-1) ^ i * ((A i).map (· ^ n)).sum) ∧
      (∀ i ≤ 2 * d, ∀ α ∈ A i,
        IsAlgebraic ℚ α ∧
        ∀ β : ℂ, Polynomial.aeval β (minpoly ℚ α) = 0 → ‖β‖ = √(Nat.card F ^ i)) :=
by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hq : 2 ≤ Nat.card F := h1
  rcases hAlt with ⟨F₁, hField₁, hAlg₁, hFinDim₁, Y, hGeomY, hPropY, hSmoothY, hProjY,
    φ, hφ_prop, hφ_surj, U, hU_ne, hU_fin, hU_et, hU_surj⟩
  letI : Field F₁ := hField₁
  letI : Algebra F F₁ := hAlg₁
  letI : FiniteDimensional F F₁ := hFinDim₁
  letI : AlgebraicGeometry.GeometricallyIrreducible Y.hom := hGeomY
  letI : AlgebraicGeometry.IsProper Y.hom := hPropY
  letI : AlgebraicGeometry.SmoothOfRelativeDimension d Y.hom := hSmoothY
  letI : Finite F₁ := Module.finite_of_finite F
  set m := Module.finrank F F₁
  have hm_pos : 0 < m := Module.finrank_pos
  have hm : 1 ≤ m := hm_pos
  have hcard : Nat.card F₁ = Nat.card F ^ m := Module.natCard_eq_pow_finrank
  let ℓ : ℕ := if ringChar F = 2 then 3 else 2
  have hPrime_ℓ : Nat.Prime ℓ := by
    dsimp [ℓ]
    split_ifs
    · exact Nat.prime_three
    · exact Nat.prime_two
  letI : Fact (Nat.Prime ℓ) := ⟨hPrime_ℓ⟩
  have hℓ_F : ℓ ≠ ringChar F := by
    dsimp [ℓ]
    split_ifs with h
    · omega
    · exact Ne.symm h
  have hchar_F₁ : CharP F₁ (ringChar F) :=
    (RingHom.charP_iff_charP (algebraMap F F₁) (ringChar F)).mp inferInstance
  have hchar_eq : ringChar F₁ = ringChar F :=
    @ringChar.eq F₁ _ (ringChar F) hchar_F₁
  have hℓ_F₁ : ℓ ≠ ringChar F₁ := by
    rw [hchar_eq]
    exact hℓ_F
  obtain ⟨M_X, hM_X0, hM_XDual, hM_XTr⟩ :=
    weil_etale_cohomology_grothendieck_package F X d ℓ hℓ_F
  obtain ⟨M_Y, -, -, -⟩ :=
    weil_etale_cohomology_grothendieck_package F₁ Y d ℓ hℓ_F₁
  have hInj : ∀ i ≤ 2 * d, ∃ f : (M_X i).V →ₗ[Padic ℓ] (M_Y i).V,
      Function.Injective f ∧ ∀ v, f (((M_X i).frob ^ m) v) = (M_Y i).frob (f v) :=
    fun i hi => weil_etale_alteration_pullback_injective F X d F₁ Y φ hφ_prop hφ_surj
      U hU_ne hU_fin hU_et hU_surj ℓ hℓ_F i hi (M_X i) (M_Y i)
  have hPureW : ∀ i ≤ 2 * d,
      ∀ γ ∈ (((M_Y i).frob).charpoly).aroots (AlgebraicClosure (Padic ℓ)),
        IsAlgebraic ℚ γ ∧
        ∀ β : ℂ, Polynomial.aeval β (minpoly ℚ γ) = 0 →
          ‖β‖ = √(((Nat.card F : ℝ) ^ m) ^ i) := by
    intro i hi γ hγ
    obtain ⟨hAlg, hNorm⟩ :=
      weil_projective_frob_eigenvalue_purity F₁ Y d hProjY ℓ hℓ_F₁ i hi (M_Y i) γ hγ
    refine ⟨hAlg, fun β hβ => ?_⟩
    rw [hNorm β hβ, hcard]
    push_cast
    rfl
  exact weil_algebraic_eigenvalue_descent_and_complex_lift
    (Padic ℓ) (Nat.card F) m d hq hm (weilPointCount F X)
    (fun i => (M_X i).V) (fun i => (M_Y i).V)
    (fun i => (M_X i).frob) (fun i => (M_Y i).frob)
    hM_X0 hM_XDual hM_XTr hInj hPureW

theorem weil_conjectures (F : Type*) [Finite F] [Field F]
    (X : Over (Spec (.of F))) [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ A : ℕ → Multiset ℂ, A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map (Nat.card F ^ d / · : ℂ → ℂ) ∧
        (∀ φ : ℂ ≃+* ℂ, (A i).map φ = A i) ∧
        ∀ α ∈ A i, IsIntegral ℤ α ∧ ‖α‖ = √(Nat.card F ^ i)) ∧
      ∀ (E : Type _) [Field E] [Algebra F E] [FiniteDimensional F E],
        Nat.card (.mk (Spec.map <| CommRingCat.ofHom <| algebraMap F E) ⟶ X) =
        ∑ i ∈ Finset.Iic (2 * d), (-1) ^ i * ((A i).map (· ^ Module.finrank F E)).sum :=
by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hq : 2 ≤ Nat.card F := h1
  have hAlt : HasSmoothProjectiveAlteration F d X :=
    weil_smooth_projective_alteration F X d
  obtain ⟨A, hA0, hDual, hTr, hPure⟩ :=
    weil_frob_eigenvalues_of_projective_alteration F X d hAlt
  obtain ⟨hExt, hZ⟩ := weil_zeta_powerSeries_integrality F X
  have hIntAut :=
    weil_integrality_and_aut_invariance_of_purity (Nat.card F) d hq
      (weilPointCount F X) A hZ hTr hPure
  refine ⟨A, hA0, ?_, ?_⟩
  · intro i hi
    exact ⟨hDual i hi, (hIntAut i hi).1, (hIntAut i hi).2⟩
  · intro E _ _ _
    obtain ⟨hPos, hCard⟩ := hExt E
    rw [hCard]
    exact hTr (Module.finrank F E) hPos

#print axioms weil_conjectures
