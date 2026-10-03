module

public import BondalThomsen.ProjectiveBundle.Fan
public import BondalThomsen.Toric.Scheme.ConeEquivalenceRays
public import BondalThomsen.Toric.Scheme.FanEquivSchemeIso
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Product
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import BondalThomsen.Toric.Scheme.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import BondalThomsen.ProjectiveBundle.Scheme
public import BondalThomsen.Toric.Divisor.LineBundleGluing

@[expose] public section

open Classical AlgebraicGeometry CategoryTheory Limits TauCeti.Toric

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ProjectiveBundle

variable {rows baseDimension columns : ℕ}

noncomputable def baseScheme (rows baseDimension : ℕ) : Scheme :=
  scheme 𝕜 (rows := rows) (baseDimension := baseDimension) (columns := 0) 0

end BondalThomsen.ProjectiveBundle
