import NatCol

open NatCol

/-- A runtime smoke test / demo of the public API, complementing the compile-time
`#guard` tests run during `lake build`. -/
def main : IO Unit := do
  IO.println "== NatSet =="
  let s := NatSet.ofList [3, 1, 4, 1, 5, 9, 2, 6, 1000]
  let t := NatSet.ofList [4, 5, 6, 7]
  IO.println s!"s             = {s.toList}"
  IO.println s!"t             = {t.toList}"
  IO.println s!"s.size        = {s.size}"
  IO.println s!"s.contains 4  = {s.contains 4}   s.contains 7 = {s.contains 7}"
  IO.println s!"s ∪ t         = {(s ∪ t).toList}"
  IO.println s!"s ∩ t         = {(s ∩ t).toList}"
  IO.println s!"t ⊆ (s ∪ t)   = {t.subset (s ∪ t)}"
  IO.println s!"erase 1000    = {(s.erase 1000).toList}"

  IO.println ""
  IO.println "== NatMap Nat =="
  let m := NatMap.ofList [(1, 10), (2, 20), (1000, 7)]
  let n := NatMap.ofList [(2, 200), (3, 30)]
  IO.println s!"m             = {repr m.toList}"
  IO.println s!"n             = {repr n.toList}"
  IO.println s!"m.get? 2      = {m.get? 2}"
  IO.println s!"m.getD 9 0    = {m.getD 9 0}"
  IO.println s!"m ⊔ n  (+)    = {repr ((m.join (· + ·) n)).toList}"
  IO.println s!"m ⊓ n  (+)    = {repr ((m.meet (· + ·) n)).toList}"
  IO.println s!"modify 2 (+5) = {repr ((m.modify 2 (· + 5))).toList}"
