module

public import Mathlib.Order.Preorder.Finite
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Basic
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice

@[expose] public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {σ τ : PointedCone ℝ V}

structure Fan (i : N →+ V) where

  lattice : IsIntegralLattice i

  cones : Set (PointedCone ℝ V)

  finite_cones : cones.Finite

  isToricCone : ∀ ⦃σ⦄, σ ∈ cones → IsToricCone i σ

  mem_of_isFaceOf : ∀ ⦃σ τ⦄, σ ∈ cones → τ.IsFaceOf σ → τ ∈ cones

  inf_isFaceOf_left : ∀ ⦃σ τ⦄, σ ∈ cones → τ ∈ cones → (σ ⊓ τ).IsFaceOf σ

namespace Fan

variable (Φ : Fan i)

@[ext]
theorem ext {Φ Ψ : Fan i} (h : Φ.cones = Ψ.cones) : Φ = Ψ := by
  cases Φ with | mk _ C _ _ _ _ =>
  cases Ψ with | mk _ D _ _ _ _ =>
  obtain rfl : C = D := h
  rfl

theorem inf_isFaceOf_right (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    (σ ⊓ τ).IsFaceOf τ :=
  inf_comm σ τ ▸ Φ.inf_isFaceOf_left hτ hσ

theorem inf_mem (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    σ ⊓ τ ∈ Φ.cones :=
  Φ.mem_of_isFaceOf hσ (Φ.inf_isFaceOf_left hσ hτ)

instance : SemilatticeInf Φ.cones :=
  Subtype.semilatticeInf fun _ _ ↦ Φ.inf_mem

@[simp, norm_cast] theorem coe_inf (σ τ : Φ.cones) :
    ((σ ⊓ τ : Φ.cones) : PointedCone ℝ V) = σ.1 ⊓ τ.1 := rfl

instance : Finite Φ.cones := Φ.finite_cones.to_subtype

theorem isFaceOf_of_le (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) (h : τ ≤ σ) : τ.IsFaceOf σ :=
  inf_eq_left.2 h ▸ Φ.inf_isFaceOf_right hτ hσ

theorem bot_mem (hσ : σ ∈ Φ.cones) : (⊥ : PointedCone ℝ V) ∈ Φ.cones :=
  Φ.mem_of_isFaceOf hσ (Φ.isToricCone hσ).salient.bot_isFaceOf

def support : Set V := ⋃ σ ∈ Φ.cones, (σ : Set V)

@[simp]
theorem mem_support {x : V} : x ∈ Φ.support ↔ ∃ σ ∈ Φ.cones, x ∈ σ := by
  simp [support]

def IsComplete : Prop := Φ.support = Set.univ

@[simp]
theorem isComplete_iff : Φ.IsComplete ↔ ∀ x : V, ∃ σ ∈ Φ.cones, x ∈ σ := by
  simp [IsComplete, Set.eq_univ_iff_forall]

end Fan

structure FanHom (Φ : Fan i) (Ψ : Fan i') where

  latticeMap : N →+ N'

  realMap : V →ₗ[ℝ] V'

  map_lattice : ∀ n, realMap (i n) = i' (latticeMap n)

  map_cone : ∀ ⦃σ⦄, σ ∈ Φ.cones → ∃ τ ∈ Ψ.cones, σ.map realMap ≤ τ

namespace FanHom

variable {Φ : Fan i} {Ψ : Fan i'}

theorem realMap_eq (f : FanHom Φ Ψ) : f.realMap = Φ.lattice.extend i' f.latticeMap :=
  Φ.lattice.eq_extend f.map_lattice

@[ext]
theorem ext {f g : FanHom Φ Ψ} (h : f.latticeMap = g.latticeMap) : f = g := by
  have hr : f.realMap = g.realMap := by rw [f.realMap_eq, g.realMap_eq, h]
  cases f with | mk fl fr _ _ =>
  cases g with | mk gl gr _ _ =>
  obtain rfl : fl = gl := h
  obtain rfl : fr = gr := hr
  rfl

protected def id (Φ : Fan i) : FanHom Φ Φ where
  latticeMap := AddMonoidHom.id N
  realMap := LinearMap.id
  map_lattice _ := rfl
  map_cone _ hσ := ⟨_, hσ, (PointedCone.map_id _).le⟩

@[simp]
theorem id_latticeMap (Φ : Fan i) : (FanHom.id Φ).latticeMap = AddMonoidHom.id N := (rfl)

@[simp]
theorem id_realMap (Φ : Fan i) : (FanHom.id Φ).realMap = LinearMap.id := (rfl)

section Comp

variable {N'' V'' : Type*} [AddCommGroup N''] [AddCommGroup V''] [Module ℝ V'']
  {i'' : N'' →+ V''} {Ω : Fan i''}

def comp (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) : FanHom Φ Ω where
  latticeMap := g.latticeMap.comp f.latticeMap
  realMap := g.realMap ∘ₗ f.realMap
  map_lattice n := by
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_comp]
    rw [f.map_lattice, g.map_lattice]
  map_cone σ hσ := by
    obtain ⟨τ, hτ, hστ⟩ := f.map_cone hσ
    obtain ⟨υ, hυ, hτυ⟩ := g.map_cone hτ
    refine ⟨υ, hυ, ?_⟩
    rw [← PointedCone.map_map]
    exact (Submodule.map_mono hστ).trans hτυ

@[simp]
theorem comp_latticeMap (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (g.comp f).latticeMap = g.latticeMap.comp f.latticeMap := (rfl)

@[simp]
theorem comp_realMap (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (g.comp f).realMap = g.realMap ∘ₗ f.realMap := (rfl)

@[simp]
theorem comp_id (f : FanHom Φ Ψ) : f.comp (FanHom.id Φ) = f := ext rfl

@[simp]
theorem id_comp (f : FanHom Φ Ψ) : (FanHom.id Ψ).comp f = f := ext rfl

variable {N''' V''' : Type*} [AddCommGroup N'''] [AddCommGroup V'''] [Module ℝ V''']
  {i''' : N''' →+ V'''} {Θ : Fan i'''}

theorem comp_assoc (h : FanHom Ω Θ) (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (h.comp g).comp f = h.comp (g.comp f) := ext rfl

end Comp

theorem exists_isLeast_cone (f : FanHom Φ Ψ) (hσ : σ ∈ Φ.cones) :
    ∃ τ, IsLeast {υ ∈ Ψ.cones | σ.map f.realMap ≤ υ} τ := by
  set T := {υ ∈ Ψ.cones | σ.map f.realMap ≤ υ}
  have hfin : T.Finite := Ψ.finite_cones.subset fun _ hυ ↦ hυ.1
  have hne : T.Nonempty := by
    obtain ⟨τ, hτ, hστ⟩ := f.map_cone hσ
    exact ⟨τ, hτ, hστ⟩
  obtain ⟨τ, hτT, hmin⟩ := hfin.exists_minimal hne
  refine ⟨τ, hτT, fun υ hυ ↦ ?_⟩
  have hinf : τ ⊓ υ ∈ T := ⟨Ψ.inf_mem hτT.1 hυ.1, le_inf hτT.2 hυ.2⟩
  exact le_trans (hmin hinf inf_le_left) inf_le_right

noncomputable def leastCone (f : FanHom Φ Ψ) (hσ : σ ∈ Φ.cones) : PointedCone ℝ V' :=
  (f.exists_isLeast_cone hσ).choose

theorem isLeast_leastCone (f : FanHom Φ Ψ) (hσ : σ ∈ Φ.cones) :
    IsLeast {υ ∈ Ψ.cones | σ.map f.realMap ≤ υ} (f.leastCone hσ) :=
  (f.exists_isLeast_cone hσ).choose_spec

theorem leastCone_mem (f : FanHom Φ Ψ) (hσ : σ ∈ Φ.cones) : f.leastCone hσ ∈ Ψ.cones :=
  (f.isLeast_leastCone hσ).1.1

theorem map_le_leastCone (f : FanHom Φ Ψ) (hσ : σ ∈ Φ.cones) :
    σ.map f.realMap ≤ f.leastCone hσ :=
  (f.isLeast_leastCone hσ).1.2

theorem leastCone_le (f : FanHom Φ Ψ) (hσ : σ ∈ Φ.cones) {υ : PointedCone ℝ V'}
    (hυ : υ ∈ Ψ.cones) (h : σ.map f.realMap ≤ υ) : f.leastCone hσ ≤ υ :=
  (f.isLeast_leastCone hσ).2 ⟨hυ, h⟩

theorem leastCone_mono (f : FanHom Φ Ψ) {τ σ : PointedCone ℝ V} (hτ : τ ∈ Φ.cones)
    (hσ : σ ∈ Φ.cones) (h : τ ≤ σ) : f.leastCone hτ ≤ f.leastCone hσ :=
  f.leastCone_le hτ (f.leastCone_mem hσ) <|
    (Submodule.map_mono h).trans (f.map_le_leastCone hσ)

theorem leastCone_isFaceOf (f : FanHom Φ Ψ) {τ σ : PointedCone ℝ V}
    (hσ : σ ∈ Φ.cones) (h : τ.IsFaceOf σ) :
    (f.leastCone (Φ.mem_of_isFaceOf hσ h)).IsFaceOf (f.leastCone hσ) :=
  Ψ.isFaceOf_of_le (f.leastCone_mem hσ)
    (f.leastCone_mem (Φ.mem_of_isFaceOf hσ h))
    (f.leastCone_mono (Φ.mem_of_isFaceOf hσ h) hσ h.le)

end FanHom

end TauCeti.Toric
