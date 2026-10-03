module

public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Regular

@[expose] public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}

namespace Fan

variable (Φ : Fan i) (Ψ : Fan i')

def prod : Fan (i.prodMap i') where
  lattice := Φ.lattice.prod Ψ.lattice
  cones := (fun p : PointedCone ℝ V × PointedCone ℝ V' ↦ p.1.prod p.2) ''
    (Φ.cones ×ˢ Ψ.cones)
  finite_cones := (Φ.finite_cones.prod Ψ.finite_cones).image _
  isToricCone σ hσ := by
    obtain ⟨⟨τ, υ⟩, ⟨hτ, hυ⟩, rfl⟩ := hσ
    exact (Φ.isToricCone hτ).prod (Ψ.isToricCone hυ)
  mem_of_isFaceOf σ τ hσ hτ := by
    obtain ⟨⟨υ, ω⟩, ⟨hυ, hω⟩, rfl⟩ := hσ
    refine ⟨⟨τ.map (.fst ℝ V V'), τ.map (.snd ℝ V V')⟩,
      ⟨Φ.mem_of_isFaceOf hυ hτ.fst, Ψ.mem_of_isFaceOf hω hτ.snd⟩, ?_⟩
    ext x
    simp only [Submodule.mem_prod, PointedCone.mem_map, LinearMap.fst_apply, Prod.exists,
      exists_and_right, exists_eq_right, LinearMap.snd_apply]
    constructor
    · simp only [and_imp, forall_exists_index]
      intro y hy z hz
      have hyz := τ.add_mem hz hy
      simp only [Prod.mk_add_mk, add_comm] at hyz
      rw [← Prod.mk_add_mk, add_comm] at hyz
      refine hτ.mem_of_add_mem_left ?_ ?_ hyz
      · exact ⟨(Submodule.mem_prod.mp (hτ.le hy)).1, (Submodule.mem_prod.mp (hτ.le hz)).2⟩
      · exact ⟨(Submodule.mem_prod.mp (hτ.le hz)).1, (Submodule.mem_prod.mp (hτ.le hy)).2⟩
    · intro hx
      exact ⟨⟨x.2, hx⟩, ⟨x.1, hx⟩⟩
  inf_isFaceOf_left σ τ hσ hτ := by
    obtain ⟨⟨σ₁, τ₁⟩, ⟨hσ₁, hτ₁⟩, rfl⟩ := hσ
    obtain ⟨⟨σ₂, τ₂⟩, ⟨hσ₂, hτ₂⟩, rfl⟩ := hτ
    simpa only [Submodule.prod_inf_prod] using
      (Φ.inf_isFaceOf_left hσ₁ hσ₂).prod (Ψ.inf_isFaceOf_left hτ₁ hτ₂)

@[simp]
theorem mem_prod_cones {ξ : PointedCone ℝ (V × V')} :
    ξ ∈ (Φ.prod Ψ).cones ↔
      ∃ σ ∈ Φ.cones, ∃ τ ∈ Ψ.cones, ξ = σ.prod τ := by
  constructor
  · rintro ⟨⟨σ, τ⟩, ⟨hσ, hτ⟩, rfl⟩
    exact ⟨σ, hσ, τ, hτ, rfl⟩
  · rintro ⟨σ, hσ, τ, hτ, rfl⟩
    exact ⟨⟨σ, τ⟩, ⟨hσ, hτ⟩, rfl⟩

theorem isComplete_prod_iff : (Φ.prod Ψ).IsComplete ↔ Φ.IsComplete ∧ Ψ.IsComplete := by
  constructor
  · intro h
    constructor
    · apply Φ.isComplete_iff.2
      intro x
      obtain ⟨ξ, hξ, hxξ⟩ := (Φ.prod Ψ).isComplete_iff.1 h (x, 0)
      obtain ⟨σ, hσ, τ, _, rfl⟩ := (Φ.mem_prod_cones Ψ).1 hξ
      exact ⟨σ, hσ, hxξ.1⟩
    · apply Ψ.isComplete_iff.2
      intro y
      obtain ⟨ξ, hξ, hyξ⟩ := (Φ.prod Ψ).isComplete_iff.1 h (0, y)
      obtain ⟨σ, _, τ, hτ, rfl⟩ := (Φ.mem_prod_cones Ψ).1 hξ
      exact ⟨τ, hτ, hyξ.2⟩
  · rintro ⟨hΦ, hΨ⟩
    apply (Φ.prod Ψ).isComplete_iff.2
    rintro ⟨x, y⟩
    obtain ⟨σ, hσ, hxσ⟩ := Φ.isComplete_iff.1 hΦ x
    obtain ⟨τ, hτ, hyτ⟩ := Ψ.isComplete_iff.1 hΨ y
    exact ⟨σ.prod τ, (Φ.mem_prod_cones Ψ).2 ⟨σ, hσ, τ, hτ, rfl⟩, ⟨hxσ, hyτ⟩⟩

theorem IsComplete.prod (hΦ : Φ.IsComplete) (hΨ : Ψ.IsComplete) : (Φ.prod Ψ).IsComplete :=
  (Φ.isComplete_prod_iff Ψ).2 ⟨hΦ, hΨ⟩

theorem IsRegular.prod (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) : (Φ.prod Ψ).IsRegular := by
  rw [isRegular_iff]
  intro ξ hξ
  obtain ⟨σ, hσ, τ, hτ, rfl⟩ := (Φ.mem_prod_cones Ψ).1 hξ
  exact ((isRegular_iff.mp hΦ) σ hσ).prod ((isRegular_iff.mp hΨ) τ hτ)

end Fan

namespace FanHom

variable {N₁ N₂ N₁' N₂' V₁ V₂ V₁' V₂' : Type*}
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₁'] [AddCommGroup N₂']
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₁'] [AddCommGroup V₂']
  [Module ℝ V₁] [Module ℝ V₂] [Module ℝ V₁'] [Module ℝ V₂']
  {i₁ : N₁ →+ V₁} {i₂ : N₂ →+ V₂} {i₁' : N₁' →+ V₁'} {i₂' : N₂' →+ V₂'}
  {Φ₁ : Fan i₁} {Φ₂ : Fan i₂} {Ψ₁ : Fan i₁'} {Ψ₂ : Fan i₂'}

def fst (Φ₁ : Fan i₁) (Φ₂ : Fan i₂) : FanHom (Φ₁.prod Φ₂) Φ₁ where
  latticeMap := AddMonoidHom.fst N₁ N₂
  realMap := LinearMap.fst ℝ V₁ V₂
  map_lattice _ := rfl
  map_cone ξ hξ := by
    obtain ⟨σ, hσ, τ, _, rfl⟩ := (Φ₁.mem_prod_cones Φ₂).1 hξ
    refine ⟨σ, hσ, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hx.1

def snd (Φ₁ : Fan i₁) (Φ₂ : Fan i₂) : FanHom (Φ₁.prod Φ₂) Φ₂ where
  latticeMap := AddMonoidHom.snd N₁ N₂
  realMap := LinearMap.snd ℝ V₁ V₂
  map_lattice _ := rfl
  map_cone ξ hξ := by
    obtain ⟨σ, _, τ, hτ, rfl⟩ := (Φ₁.mem_prod_cones Φ₂).1 hξ
    refine ⟨τ, hτ, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hx.2

section Prod

variable {N₀ V₀ : Type*} [AddCommGroup N₀] [AddCommGroup V₀] [Module ℝ V₀]
  {i₀ : N₀ →+ V₀} {Ω : Fan i₀}

def prod (f : FanHom Ω Φ₁) (g : FanHom Ω Φ₂) : FanHom Ω (Φ₁.prod Φ₂) where
  latticeMap := f.latticeMap.prod g.latticeMap
  realMap := f.realMap.prod g.realMap
  map_lattice n := by
    simp only [LinearMap.prod_apply, Function.prod_apply, AddMonoidHom.prod_apply,
      AddMonoidHom.coe_prodMap, Prod.map_apply', f.map_lattice, g.map_lattice]
  map_cone ξ hξ := by
    obtain ⟨σ, hσ, hξσ⟩ := f.map_cone hξ
    obtain ⟨τ, hτ, hξτ⟩ := g.map_cone hξ
    refine ⟨σ.prod τ, (Φ₁.mem_prod_cones Φ₂).2 ⟨σ, hσ, τ, hτ, rfl⟩, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact ⟨hξσ ⟨x, hx, rfl⟩, hξτ ⟨x, hx, rfl⟩⟩

end Prod

def prodMap (f : FanHom Φ₁ Ψ₁) (g : FanHom Φ₂ Ψ₂) : FanHom (Φ₁.prod Φ₂) (Ψ₁.prod Ψ₂) where
  latticeMap := f.latticeMap.prodMap g.latticeMap
  realMap := f.realMap.prodMap g.realMap
  map_lattice n := by
    simp only [LinearMap.prodMap_apply, AddMonoidHom.coe_prodMap, Prod.map_apply', f.map_lattice,
      g.map_lattice]
  map_cone ξ hξ := by
    obtain ⟨σ, hσ, τ, hτ, rfl⟩ := (Φ₁.mem_prod_cones Φ₂).1 hξ
    obtain ⟨σ', hσ', hleσ⟩ := f.map_cone hσ
    obtain ⟨τ', hτ', hleτ⟩ := g.map_cone hτ
    refine ⟨σ'.prod τ', (Ψ₁.mem_prod_cones Ψ₂).2 ⟨σ', hσ', τ', hτ', rfl⟩, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨hleσ ⟨x.1, hx.1, rfl⟩, hleτ ⟨x.2, hx.2, rfl⟩⟩

end FanHom

end TauCeti.Toric
