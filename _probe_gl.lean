import PvsNP.Basic
#check List.getElem_mapIdx
#check List.getElem_map
example (x : List Bool) (f : ℕ → Bool → F4) (i : ℕ) (h : i < x.length) :
    (x.mapIdx (fun j b => f j b)).get ⟨i, h⟩ = f i (x.get ⟨i, h⟩) := by
  rw [List.getElem_mapIdx]
