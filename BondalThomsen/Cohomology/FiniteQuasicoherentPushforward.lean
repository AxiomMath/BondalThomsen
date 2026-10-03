module

public import BondalThomsen.Cohomology.AffineQuasicoherentCohomologyVanishing
public import BondalThomsen.Toric.Frobenius.MultiplicationCohomologyTransport
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Sites.LocalProperties

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

namespace BondalThomsen.FiniteQuasicoherentPushforward

universe u

noncomputable section

variable {SourceRing TargetRing : CommRingCat.{u}}

theorem specPushforward_isQuasicoherent (ring_map : TargetRing ⟶ SourceRing)
    (coefficient : (Spec SourceRing).Modules) [coefficient.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map ring_map)).obj coefficient).IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
    (isIso_fromTildeΓ_pushforward ring_map coefficient)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def specPushforwardGlobalSectionsIso (ring_map : TargetRing ⟶ SourceRing)
    (coefficient : (Spec SourceRing).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map ring_map)).obj coefficient) ≅
      (ModuleCat.restrictScalars ring_map.hom).obj (moduleSpecΓFunctor.obj coefficient) := by
  let pushed_sections := moduleSpecΓFunctor.obj
    ((Scheme.Modules.pushforward (Spec.map ring_map)).obj coefficient)
  let restricted_sections := (ModuleCat.restrictScalars ring_map.hom).obj
    (moduleSpecΓFunctor.obj coefficient)
  letI : Module TargetRing pushed_sections := pushed_sections.isModule
  letI : Module TargetRing restricted_sections := restricted_sections.isModule
  refine (show pushed_sections ≃ₗ[TargetRing] restricted_sections from
    { toFun := fun element => element
      invFun := fun element => element
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }).toModuleIso
  intro scalar element
  change coefficient.val.obj (op ⊤) at element
  let : Module (Γ(Spec SourceRing, ⊤)) (coefficient.val.obj (op ⊤)) :=
    (coefficient.val.obj (op ⊤)).isModule
  change (Spec.map ring_map).appTop ((Scheme.ΓSpecIso TargetRing).inv scalar) • element =
    (Scheme.ΓSpecIso SourceRing).inv (ring_map scalar) • element
  have equality := Scheme.ΓSpecIso_inv_naturality ring_map
  exact congrArg (fun value : Γ(Spec SourceRing, ⊤) => value • element)
    (congrArg (fun arrow => arrow scalar) equality).symm

set_option backward.isDefEq.respectTransparency false in
def specPushforwardGlobalSectionsNatIso (ring_map : TargetRing ⟶ SourceRing) :
    Scheme.Modules.pushforward (Spec.map ring_map) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars ring_map.hom :=
  NatIso.ofComponents (specPushforwardGlobalSectionsIso ring_map) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
theorem specPushforward_epi (ring_map : TargetRing ⟶ SourceRing)
    {first second : (Spec SourceRing).Modules}
    [first.IsQuasicoherent] [second.IsQuasicoherent]
    (coefficient_map : first ⟶ second) [Epi coefficient_map] :
    Epi ((Scheme.Modules.pushforward (Spec.map ring_map)).map coefficient_map) := by
  let := specPushforward_isQuasicoherent ring_map first
  let := specPushforward_isQuasicoherent ring_map second
  let : Epi (moduleSpecΓFunctor.map coefficient_map) :=
    AffineQuasicoherentCohomologyVanishing.quasicoherentGlobalSections_epi coefficient_map
  let comparison := specPushforwardGlobalSectionsNatIso ring_map
  have equality := comparison.hom.naturality coefficient_map
  let : Epi ((Scheme.Modules.pushforward (Spec.map ring_map) ⋙ moduleSpecΓFunctor).map
      coefficient_map ≫ comparison.hom.app second) := by
    rw [equality]
    change Epi (comparison.hom.app first ≫
      (ModuleCat.restrictScalars ring_map.hom).map (moduleSpecΓFunctor.map coefficient_map))
    infer_instance
  let : Epi (moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward (Spec.map ring_map)).map coefficient_map)) :=
    (epi_comp_iff_of_isIso _ (comparison.hom.app second)).mp
      (inferInstanceAs (Epi ((Scheme.Modules.pushforward (Spec.map ring_map) ⋙
        moduleSpecΓFunctor).map coefficient_map ≫ comparison.hom.app second)))
  have naturality := Scheme.Modules.fromTildeΓNatTrans.naturality
    ((Scheme.Modules.pushforward (Spec.map ring_map)).map coefficient_map)
  change (tilde.functor TargetRing).map (moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward (Spec.map ring_map)).map coefficient_map)) ≫
      ((Scheme.Modules.pushforward (Spec.map ring_map)).obj second).fromTildeΓ =
    ((Scheme.Modules.pushforward (Spec.map ring_map)).obj first).fromTildeΓ ≫
      (Scheme.Modules.pushforward (Spec.map ring_map)).map coefficient_map at naturality
  let : Epi (((Scheme.Modules.pushforward (Spec.map ring_map)).obj first).fromTildeΓ ≫
      (Scheme.Modules.pushforward (Spec.map ring_map)).map coefficient_map) := by
    rw [← naturality]
    infer_instance
  exact epi_of_epi (((Scheme.Modules.pushforward (Spec.map ring_map)).obj first).fromTildeΓ) _

variable {Source Target : Scheme.{u}}

def schemeIsoModulesEquivalence (scheme_iso : Source ≅ Target) :
    Source.Modules ≌ Target.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward scheme_iso.hom)
    (Scheme.Modules.pushforward scheme_iso.inv)
    (Scheme.Modules.pushforwardComp _ _ ≪≫
      Scheme.Modules.pushforwardCongr scheme_iso.hom_inv_id ≪≫
        Scheme.Modules.pushforwardId Source).symm
    (Scheme.Modules.pushforwardComp _ _ ≪≫
      Scheme.Modules.pushforwardCongr scheme_iso.inv_hom_id ≪≫
        Scheme.Modules.pushforwardId Target)

def schemeIsoPushforwardRestrictIso (scheme_iso : Source ≅ Target) :
    Scheme.Modules.pushforward scheme_iso.hom ≅ Scheme.Modules.restrictFunctor scheme_iso.inv :=
  (schemeIsoModulesEquivalence scheme_iso).toAdjunction.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction scheme_iso.inv)

theorem schemeIsoPushforward_isQuasicoherent (scheme_iso : Source ≅ Target)
    (coefficient : Source.Modules) [coefficient.IsQuasicoherent] :
    ((Scheme.Modules.pushforward scheme_iso.hom).obj coefficient).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Target.ringCatSheaf).prop_of_iso
    ((schemeIsoPushforwardRestrictIso scheme_iso).symm.app coefficient) inferInstance

set_option backward.isDefEq.respectTransparency false in
def affinePushforwardSpecComparison (morphism : Source ⟶ Target)
    [IsAffine Source] [IsAffine Target] :
    Scheme.Modules.pushforward morphism ⋙ Scheme.Modules.pushforward Target.isoSpec.hom ≅
      Scheme.Modules.pushforward Source.isoSpec.hom ⋙
        Scheme.Modules.pushforward (Spec.map morphism.appTop) :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (Scheme.isoSpec_hom_naturality morphism).symm ≪≫
    (Scheme.Modules.pushforwardComp _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem affineSchemesPushforward_isQuasicoherent (morphism : Source ⟶ Target)
    [IsAffine Source] [IsAffine Target] (coefficient : Source.Modules)
    [coefficient.IsQuasicoherent] :
    ((Scheme.Modules.pushforward morphism).obj coefficient).IsQuasicoherent := by
  let source_coefficient := (Scheme.Modules.pushforward Source.isoSpec.hom).obj coefficient
  let := schemeIsoPushforward_isQuasicoherent Source.isoSpec coefficient
  let := specPushforward_isQuasicoherent morphism.appTop source_coefficient
  let : ((Scheme.Modules.pushforward Target.isoSpec.hom).obj
      ((Scheme.Modules.pushforward morphism).obj coefficient)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent.{u} (Spec Γ(Target, ⊤)).ringCatSheaf).prop_of_iso
      ((affinePushforwardSpecComparison morphism).symm.app coefficient)
      (inferInstanceAs (SheafOfModules.IsQuasicoherent.{u}
        ((Scheme.Modules.pushforward (Spec.map morphism.appTop)).obj source_coefficient)))
  exact (SheafOfModules.isQuasicoherent Target.ringCatSheaf).prop_of_iso
    ((schemeIsoModulesEquivalence Target.isoSpec).unitIso.symm.app
      ((Scheme.Modules.pushforward morphism).obj coefficient))
    (schemeIsoPushforward_isQuasicoherent Target.isoSpec.symm
      ((Scheme.Modules.pushforward Target.isoSpec.hom).obj
        ((Scheme.Modules.pushforward morphism).obj coefficient)))

set_option backward.isDefEq.respectTransparency false in
theorem affineSchemesPushforward_epi (morphism : Source ⟶ Target)
    [IsAffine Source] [IsAffine Target] {first second : Source.Modules}
    [first.IsQuasicoherent] [second.IsQuasicoherent]
    (coefficient_map : first ⟶ second) [Epi coefficient_map] :
    Epi ((Scheme.Modules.pushforward morphism).map coefficient_map) := by
  let : (Scheme.Modules.pushforward Source.isoSpec.hom).IsEquivalence :=
    (schemeIsoModulesEquivalence Source.isoSpec).isEquivalence_functor
  let : (Scheme.Modules.pushforward Target.isoSpec.hom).IsEquivalence :=
    (schemeIsoModulesEquivalence Target.isoSpec).isEquivalence_functor
  let := schemeIsoPushforward_isQuasicoherent Source.isoSpec first
  let := schemeIsoPushforward_isQuasicoherent Source.isoSpec second
  let := specPushforward_epi morphism.appTop
    ((Scheme.Modules.pushforward Source.isoSpec.hom).map coefficient_map)
  let comparison := affinePushforwardSpecComparison morphism
  have equality := comparison.hom.naturality coefficient_map
  let : Epi ((Scheme.Modules.pushforward morphism ⋙
      Scheme.Modules.pushforward Target.isoSpec.hom).map coefficient_map ≫
        comparison.hom.app second) := by
    rw [equality]
    change Epi (comparison.hom.app first ≫
      (Scheme.Modules.pushforward (Spec.map morphism.appTop)).map
        ((Scheme.Modules.pushforward Source.isoSpec.hom).map coefficient_map))
    infer_instance
  let : Epi ((Scheme.Modules.pushforward Target.isoSpec.hom).map
      ((Scheme.Modules.pushforward morphism).map coefficient_map)) :=
    (epi_comp_iff_of_isIso _ (comparison.hom.app second)).mp
      (inferInstanceAs (Epi ((Scheme.Modules.pushforward morphism ⋙
        Scheme.Modules.pushforward Target.isoSpec.hom).map coefficient_map ≫
          comparison.hom.app second)))
  exact (Scheme.Modules.pushforward Target.isoSpec.hom).epi_of_epi_map inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem isQuasicoherent_of_openImmersionRestriction
    (open_map : Source ⟶ Target) [IsOpenImmersion open_map]
    (coefficient : Target.Modules) [(coefficient.restrict open_map).IsQuasicoherent] :
    (coefficient.over open_map.opensRange).IsQuasicoherent := by
  let transport := Scheme.Modules.restrictFunctor open_map.isoOpensRange.inv ⋙
    (Scheme.Modules.overEquiv open_map.opensRange).inverse
  let : (transport.obj (coefficient.restrict open_map)).IsQuasicoherent := by
    let restricted := (coefficient.restrict open_map).restrict open_map.isoOpensRange.inv
    let : restricted.IsQuasicoherent := inferInstance
    let open_range : Opens (Target : Type u) := open_map.opensRange
    let : Functor.IsDenseSubsite
        ((Opens.grothendieckTopology (Target : Type u)).over open_range)
        (Opens.grothendieckTopology open_range.carrier)
        open_range.overEquivalence.functor :=
      Opens.instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
        open_range
    let : open_range.overEquivalence.functor.IsContinuous
        ((Opens.grothendieckTopology (Target : Type u)).over open_range)
        (Opens.grothendieckTopology open_range.carrier) :=
      Functor.IsDenseSubsite.instIsContinuous _ _ _
    let (local_open : Over open_map.opensRange) :
        (Over.post open_map.opensRange.overEquivalence.functor).IsContinuous
          (((Opens.grothendieckTopology Target).over open_map.opensRange).over local_open)
          ((Opens.grothendieckTopology open_range.carrier).over
            (open_map.opensRange.overEquivalence.functor.obj local_open)) :=
      Functor.isContinuous_of_coverPreserving
        (compatiblePreservingOfDownwardsClosed
          ((Opens.grothendieckTopology open_range.carrier).over
            (open_range.overEquivalence.functor.obj local_open))
          (Over.post open_range.overEquivalence.functor) (fun {_} {local_target} _ =>
          ⟨(Over.postEquiv local_open open_range.overEquivalence).inverse.obj local_target,
            (Over.postEquiv local_open open_range.overEquivalence).counitIso.app local_target⟩))
        ((CoverPreserving.of_isContinuous open_range.overEquivalence.functor
          ((Opens.grothendieckTopology Target).over open_map.opensRange)
          (Opens.grothendieckTopology open_range.carrier)).overPost local_open)
    exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      open_map.opensRange.overEquivalence.functor
      (open_map.opensRange.sheafRestrictSheafEquivOver.app Target.ringCatSheaf).inv
      (Opens.sheafOfModulesEquivOverInverseUnit open_map.opensRange Target.ringCatSheaf)
      (M := restricted)
  exact (SheafOfModules.isQuasicoherent.{u} (Target.ringCatSheaf.over open_map.opensRange)).prop_of_iso
    (BondalThomsen.openImmersionOverRestrictionIso open_map coefficient) inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem isQuasicoherent_of_openCover (cover : Scheme.OpenCover.{u} Target)
    (coefficient : Target.Modules)
    [∀ index, (coefficient.restrict (cover.f index)).IsQuasicoherent] :
    coefficient.IsQuasicoherent := by
  let (index : cover.I₀) : (coefficient.over (cover.f index).opensRange).IsQuasicoherent :=
    isQuasicoherent_of_openImmersionRestriction (cover.f index) coefficient
  exact SheafOfModules.IsQuasicoherent.of_coversTop coefficient
    (fun index => (cover.f index).opensRange) (by
      exact (Opens.coversTop_iff _ _).mpr cover.isOpenCover_opensRange)

set_option backward.isDefEq.respectTransparency false in
theorem affinePushforward_isQuasicoherent (morphism : Source ⟶ Target)
    [IsAffineHom morphism] (coefficient : Source.Modules)
    [coefficient.IsQuasicoherent] :
    ((Scheme.Modules.pushforward morphism).obj coefficient).IsQuasicoherent := by
  let cover := Target.affineCover
  let (index : cover.I₀) :
      (((Scheme.Modules.pushforward morphism).obj coefficient).restrict
        (cover.f index)).IsQuasicoherent := by
    let : IsAffine (pullback morphism (cover.f index)) := inferInstance
    let := affineSchemesPushforward_isQuasicoherent
      (pullback.snd morphism (cover.f index))
      (coefficient.restrict (pullback.fst morphism (cover.f index)))
    exact (SheafOfModules.isQuasicoherent.{u} (cover.X index).ringCatSheaf).prop_of_iso
      (BondalThomsen.openPullbackPushforwardRestrictIso
        (IsPullback.of_hasPullback morphism (cover.f index)).flip coefficient).symm
      inferInstance
  exact isQuasicoherent_of_openCover cover _

set_option backward.isDefEq.respectTransparency false in
theorem hom_ext_of_openCover (cover : Scheme.OpenCover.{u} Target)
    {first second : Target.Modules} (first_map second_map : first ⟶ second)
    (local_equality : ∀ index, (Scheme.Modules.restrictFunctor (cover.f index)).map first_map =
      (Scheme.Modules.restrictFunctor (cover.f index)).map second_map) :
    first_map = second_map := by
  let covers_top : (Opens.grothendieckTopology Target).CoversTop
      (fun index => (cover.f index).opensRange) :=
    (Opens.coversTop_iff _ _).mpr cover.isOpenCover_opensRange
  apply Scheme.Modules.hom_ext
  intro open_set
  apply second.isSheaf.hom_ext (covers_top.cover open_set)
  rintro ⟨local_open, inclusion, ⟨index, ⟨inside⟩⟩⟩
  have equality := congrArg
    (fun arrow => arrow.app ((cover.f index) ⁻¹ᵁ local_open)) (local_equality index)
  change first_map.app ((cover.f index) ''ᵁ (cover.f index) ⁻¹ᵁ local_open) =
    second_map.app ((cover.f index) ''ᵁ (cover.f index) ⁻¹ᵁ local_open) at equality
  rw [(cover.f index).image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr inside.le] at equality
  change first_map.mapPresheaf.app (op open_set) ≫ second.presheaf.map inclusion.op =
    second_map.mapPresheaf.app (op open_set) ≫ second.presheaf.map inclusion.op
  rw [← first_map.mapPresheaf.naturality, ← second_map.mapPresheaf.naturality]
  exact congrArg (fun arrow => first.presheaf.map inclusion.op ≫ arrow) equality

theorem epi_of_openCover (cover : Scheme.OpenCover.{u} Target)
    {first second : Target.Modules} (coefficient_map : first ⟶ second)
    [∀ index, Epi ((Scheme.Modules.restrictFunctor (cover.f index)).map coefficient_map)] :
    Epi coefficient_map := by
  constructor
  intro third first_map second_map equality
  apply hom_ext_of_openCover cover
  intro index
  apply (cancel_epi ((Scheme.Modules.restrictFunctor (cover.f index)).map
    coefficient_map)).mp
  simpa only [← Functor.map_comp] using
    congrArg (fun arrow => (Scheme.Modules.restrictFunctor (cover.f index)).map arrow) equality

set_option backward.isDefEq.respectTransparency false in
def openPullbackPushforwardRestrictNatIso
    {LocalSource LocalTarget : Scheme.{u}}
    {morphism : Source ⟶ Target} {local_morphism : LocalSource ⟶ LocalTarget}
    {source_open : LocalSource ⟶ Source} {target_open : LocalTarget ⟶ Target}
    [IsOpenImmersion source_open] [IsOpenImmersion target_open]
    (square : IsPullback local_morphism source_open target_open morphism) :
    Scheme.Modules.pushforward morphism ⋙ Scheme.Modules.restrictFunctor target_open ≅
      Scheme.Modules.restrictFunctor source_open ⋙
        Scheme.Modules.pushforward local_morphism := by
  let comparison := Functor.whiskerRight
    (Functor.whiskerRight (Scheme.Modules.restrictAdjunction source_open).unit
      (Scheme.Modules.pushforward morphism))
    (Scheme.Modules.restrictFunctor target_open)
  letI (coefficient : Source.Modules) : IsIso (comparison.app coefficient) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro open_set
    have image_eq :
        source_open ''ᵁ source_open ⁻¹ᵁ (morphism ⁻¹ᵁ target_open ''ᵁ open_set) =
          morphism ⁻¹ᵁ target_open ''ᵁ open_set := by
      rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback square open_set,
        source_open.preimage_image_eq]
    change IsIso (coefficient.presheaf.map
      (homOfLE (source_open.image_preimage_le
        (morphism ⁻¹ᵁ target_open ''ᵁ open_set))).op)
    have inclusion_eq : homOfLE (source_open.image_preimage_le
        (morphism ⁻¹ᵁ target_open ''ᵁ open_set)) = eqToHom image_eq := Subsingleton.elim _ _
    rw [inclusion_eq]
    infer_instance
  exact (NatIso.ofComponents (fun coefficient => asIso (comparison.app coefficient))
      (by intros; exact comparison.naturality _)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor source_open)
      (Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp source_open morphism)
        (Scheme.Modules.restrictFunctor target_open)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor source_open)
      (Functor.isoWhiskerRight (Scheme.Modules.pushforwardCongr square.w.symm)
        (Scheme.Modules.restrictFunctor target_open)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor source_open)
      (Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp local_morphism target_open).symm
        (Scheme.Modules.restrictFunctor target_open)) ≪≫
    Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor source_open ⋙ Scheme.Modules.pushforward local_morphism)
      (Scheme.Modules.restrictFunctorAdjCounitIso target_open)

set_option backward.isDefEq.respectTransparency false in
theorem affinePushforward_epi (morphism : Source ⟶ Target) [IsAffineHom morphism]
    {first second : Source.Modules} [first.IsQuasicoherent] [second.IsQuasicoherent]
    (coefficient_map : first ⟶ second) [Epi coefficient_map] :
    Epi ((Scheme.Modules.pushforward morphism).map coefficient_map) := by
  let cover := Target.affineCover
  let (index : cover.I₀) : Epi ((Scheme.Modules.restrictFunctor (cover.f index)).map
      ((Scheme.Modules.pushforward morphism).map coefficient_map)) := by
    let : IsAffine (pullback morphism (cover.f index)) := inferInstance
    let := affineSchemesPushforward_epi (pullback.snd morphism (cover.f index))
      ((Scheme.Modules.restrictFunctor (pullback.fst morphism (cover.f index))).map
        coefficient_map)
    let comparison := openPullbackPushforwardRestrictNatIso
      (IsPullback.of_hasPullback morphism (cover.f index)).flip
    have equality := comparison.hom.naturality coefficient_map
    let : Epi ((Scheme.Modules.pushforward morphism ⋙
        Scheme.Modules.restrictFunctor (cover.f index)).map coefficient_map ≫
          comparison.hom.app second) := by
      rw [equality]
      change Epi (comparison.hom.app first ≫
        (Scheme.Modules.pushforward (pullback.snd morphism (cover.f index))).map
          ((Scheme.Modules.restrictFunctor (pullback.fst morphism (cover.f index))).map
            coefficient_map))
      infer_instance
    exact (epi_comp_iff_of_isIso _ (comparison.hom.app second)).mp
      (inferInstanceAs (Epi ((Scheme.Modules.pushforward morphism ⋙
        Scheme.Modules.restrictFunctor (cover.f index)).map coefficient_map ≫
          comparison.hom.app second)))
  exact epi_of_openCover cover _

theorem affinePushforward_shortExact (morphism : Source ⟶ Target) [IsAffineHom morphism]
    {sequence : ShortComplex Source.Modules}
    [sequence.X₁.IsQuasicoherent] [sequence.X₂.IsQuasicoherent]
    [sequence.X₃.IsQuasicoherent] (exact_sequence : sequence.ShortExact) :
    (sequence.map (Scheme.Modules.pushforward morphism)).ShortExact := by
  let : Epi sequence.g := exact_sequence.epi_g
  let := affinePushforward_epi morphism sequence.g
  exact ToricMultiplicationCohomologyTransport.pushforward_shortExact_of_epi _ exact_sequence

end

end BondalThomsen.FiniteQuasicoherentPushforward

