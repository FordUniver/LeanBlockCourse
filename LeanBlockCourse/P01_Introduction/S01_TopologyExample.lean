import Mathlib.Topology.Basic

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example {f : X → Y} {g: Y → Z}
        (hf : Continuous f) (hg : Continuous g) :
        Continuous (g ∘ f) := by

  constructor
  intros U hU
  
  let V := g⁻¹' U
  have hV : IsOpen V := hg.isOpen_preimage U hU

  let W := f⁻¹' V
  have hW : IsOpen W := hf.isOpen_preimage V hV

  have : W = (g ∘ f)⁻¹' U := rfl  
  rw [← this]

  exact hW  

example {f : X → Y} {g: Y → Z}
        (hf : Continuous f) (hg : Continuous g) :
        Continuous (g ∘ f) := by
  constructor
  intros U hU

  have hV : IsOpen (g⁻¹' U) := hg.isOpen_preimage U hU
  have hW : IsOpen (f⁻¹' (g⁻¹' U)) := hf.isOpen_preimage (g⁻¹' U) hV

  exact hW  
  
example {f : X → Y} {g: Y → Z}
        (hf : Continuous f) (hg : Continuous g) :
        Continuous (g ∘ f) := by
  constructor
  intros U hU
  exact hf.isOpen_preimage (g⁻¹' U) (hg.isOpen_preimage U hU)

example {f : X → Y} {g: Y → Z}
        (hf : Continuous f) (hg : Continuous g) :
        Continuous (g ∘ f) :=
  { isOpen_preimage := λ U hU => hf.isOpen_preimage (g⁻¹' U) (hg.isOpen_preimage U hU) }
