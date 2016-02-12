sig Element

sig Set{
	elements: set Element
}
sig Multiset extends Set{
	multiplicity: elements -> Int
}

sig Sequence extends Set{
	position: elements -> set Int
}

assert Closed {
	 all s0, s1: Set | some s2: Set |
		 s2.elements = s0.elements + s1.elements
	 }

fact SetGenerator {
	 some s: Set | no s.elements
	 all s: Set, e: Element |
		 some s’: Set | s’.elements = s.elements + e
	 }
